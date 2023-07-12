#![feature(rustc_private)]
use crate::{
    control_flow::{
        cfg::{CallSite, Edge, EdgeKind, ForwardCFG, Method, Node, NodeKind},
        utils,
    },
    known_names::KnownNames,
};
use either::*;
use log::*;
//use rustc_hir::Constness;
//use rustc_middle::ty::TyCtxtExt;
//use rustc_middle::ty::context::TyCtxtExt;

use rustc_infer::{
    //infer::InferCtxt,
    infer::{InferCtxt,TyCtxtInferExt}, //InferOk
    traits::{FulfillmentErrorCode, Obligation, ObligationCause},
};
use rustc_middle::ty::subst::{GenericArg, GenericArgKind, InternalSubsts, SubstsRef};
use rustc_middle::ty::Clause; //modify 04-2
use rustc_middle::ty::{GlobalCtxt, TyCtxt}; //TyCtxt,  modify
use rustc_middle::{
    mir::{
        self,
        *, //self,
           //terminator::{Terminator, TerminatorKind},
           //BasicBlockData, Body, START_BLOCK,
    },
    ty::{
        error::TypeError,
        //subst::{GenericArg, GenericArgKind, InternalSubsts, SubstsRef},//Substs,  modify PredicateKind,
        AssocKind,
        GenericPredicates,
        Instance,
        InstanceDef,
        ParamEnv,
        ToPredicate,
        TraitPredicate,
        TraitRef,
        TyKind,
        TypeAndMut,
        Predicate,
        PredicateKind,
    },
}; //Substs
   //use  rustc_middle::ty::AliasKind;    //modify 04-1
use rustc_middle::ty::*;
use rustc_middle::ty;
use rustc_middle::bug;
//use std::ops::Deref;
//use rustc_middle::ty::subst::Substs;    //modify delete this line

use rustc_span::def_id::DefId;
use rustc_trait_selection::traits::{FulfillmentContext, TraitEngine,TraitEngineExt};
use std::{
    collections::{HashMap, HashSet, LinkedList},
    iter::FromIterator, any::type_name, //env::home_dir,
};

//use std::ops::Deref;


struct SubstFolder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    substs: &'a [GenericArg<'tcx>],

    /// Number of region binders we have passed through while doing the substitution
    binders_passed: u32,
}

impl<'a, 'tcx> TypeFolder<'tcx> for SubstFolder<'a, 'tcx> {
    #[inline]
    fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<'tcx>>(
        &mut self,
        t: ty::Binder<'tcx, T>,
    ) -> ty::Binder<'tcx, T> {
        self.binders_passed += 1;
        let t = t.super_fold_with(self);
        self.binders_passed -= 1;
        t
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        #[cold]
        #[inline(never)]
        fn region_param_out_of_range(data: ty::EarlyBoundRegion, substs: &[GenericArg<'_>]) -> ! {
            bug!(
                "Region parameter out of range when substituting in region {} (index={}, substs = {:?})",
                data.name,
                data.index,
                substs,
            )
        }

        #[cold]
        #[inline(never)]
        fn region_param_invalid(data: ty::EarlyBoundRegion, other: GenericArgKind<'_>) -> ! {
            bug!(
                "Unexpected parameter {:?} when substituting in region {} (index={})",
                other,
                data.name,
                data.index
            )
        }

        // Note: This routine only handles regions that are bound on
        // type declarations and other outer declarations, not those
        // bound in *fn types*. Region substitution of the bound
        // regions that appear in a function signature is done using
        // the specialized routine `ty::replace_late_regions()`.
        match *r {
            ty::ReEarlyBound(data) => {
                let rk = self.substs.get(data.index as usize).map(|k| k.unpack());
                match rk {
                    Some(GenericArgKind::Lifetime(lt)) => self.shift_region_through_binders(lt),
                    Some(other) => region_param_invalid(data, other),
                    None => region_param_out_of_range(data, self.substs),
                }
            }
            _ => r,
        }
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        if !t.needs_subst() {
            return t;
        }

        match *t.kind() {
            ty::Param(p) => self.ty_for_param(p, t),
            _ => t.super_fold_with(self),
        }
    }

    fn fold_const(&mut self, c: ty::Const<'tcx>) -> ty::Const<'tcx> {
        if let ty::ConstKind::Param(p) = c.kind() {
            self.const_for_param(p, c)
        } else {
            c.super_fold_with(self)
        }
    }
}

impl<'a, 'tcx> SubstFolder<'a, 'tcx> {
    fn ty_for_param(&self, p: ty::ParamTy, source_ty: Ty<'tcx>) -> Ty<'tcx> {
        // Look up the type in the substitutions. It really should be in there.
        let opt_ty = self.substs.get(p.index as usize).map(|k| k.unpack());
        let ty = match opt_ty {
            Some(GenericArgKind::Type(ty)) => ty,
            Some(kind) => self.type_param_expected(p, source_ty, kind),
            None => self.type_param_out_of_range(p, source_ty),
        };

        self.shift_vars_through_binders(ty)
    }

    #[cold]
    #[inline(never)]
    fn type_param_expected(&self, p: ty::ParamTy, ty: Ty<'tcx>, kind: GenericArgKind<'tcx>) -> ! {
        bug!(
            "expected type for `{:?}` ({:?}/{}) but found {:?} when substituting, substs={:?}",
            p,
            ty,
            p.index,
            kind,
            self.substs,
        )
    }

    #[cold]
    #[inline(never)]
    fn type_param_out_of_range(&self, p: ty::ParamTy, ty: Ty<'tcx>) -> ! {
        bug!(
            "type parameter `{:?}` ({:?}/{}) out of range when substituting, substs={:?}",
            p,
            ty,
            p.index,
            self.substs,
        )
    }

    fn const_for_param(&self, p: ParamConst, source_ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
        // Look up the const in the substitutions. It really should be in there.
        let opt_ct = self.substs.get(p.index as usize).map(|k| k.unpack());
        let ct = match opt_ct {
            Some(GenericArgKind::Const(ct)) => ct,
            Some(kind) => self.const_param_expected(p, source_ct, kind),
            None => self.const_param_out_of_range(p, source_ct),
        };

        self.shift_vars_through_binders(ct)
    }

    #[cold]
    #[inline(never)]
    fn const_param_expected(
        &self,
        p: ty::ParamConst,
        ct: ty::Const<'tcx>,
        kind: GenericArgKind<'tcx>,
    ) -> ! {
        bug!(
            "expected const for `{:?}` ({:?}/{}) but found {:?} when substituting substs={:?}",
            p,
            ct,
            p.index,
            kind,
            self.substs,
        )
    }

    #[cold]
    #[inline(never)]
    fn const_param_out_of_range(&self, p: ty::ParamConst, ct: ty::Const<'tcx>) -> ! {
        bug!(
            "const parameter `{:?}` ({:?}/{}) out of range when substituting substs={:?}",
            p,
            ct,
            p.index,
            self.substs,
        )
    }

    /// It is sometimes necessary to adjust the De Bruijn indices during substitution. This occurs
    /// when we are substituting a type with escaping bound vars into a context where we have
    /// passed through binders. That's quite a mouthful. Let's see an example:
    ///
    /// ```
    /// type Func<A> = fn(A);
    /// type MetaFunc = for<'a> fn(Func<&'a i32>);
    /// ```
    ///
    /// The type `MetaFunc`, when fully expanded, will be
    /// ```ignore (illustrative)
    /// for<'a> fn(fn(&'a i32))
    /// //      ^~ ^~ ^~~
    /// //      |  |  |
    /// //      |  |  DebruijnIndex of 2
    /// //      Binders
    /// ```
    /// Here the `'a` lifetime is bound in the outer function, but appears as an argument of the
    /// inner one. Therefore, that appearance will have a DebruijnIndex of 2, because we must skip
    /// over the inner binder (remember that we count De Bruijn indices from 1). However, in the
    /// definition of `MetaFunc`, the binder is not visible, so the type `&'a i32` will have a
    /// De Bruijn index of 1. It's only during the substitution that we can see we must increase the
    /// depth by 1 to account for the binder that we passed through.
    ///
    /// As a second example, consider this twist:
    ///
    /// ```
    /// type FuncTuple<A> = (A,fn(A));
    /// type MetaFuncTuple = for<'a> fn(FuncTuple<&'a i32>);
    /// ```
    ///
    /// Here the final type will be:
    /// ```ignore (illustrative)
    /// for<'a> fn((&'a i32, fn(&'a i32)))
    /// //          ^~~         ^~~
    /// //          |           |
    /// //   DebruijnIndex of 1 |
    /// //               DebruijnIndex of 2
    /// ```
    /// As indicated in the diagram, here the same type `&'a i32` is substituted once, but in the
    /// first case we do not increase the De Bruijn index and in the second case we do. The reason
    /// is that only in the second case have we passed through a fn binder.
    fn shift_vars_through_binders<T: TypeFoldable<'tcx>>(&self, val: T) -> T {
        debug!(
            "shift_vars(val={:?}, binders_passed={:?}, has_escaping_bound_vars={:?})",
            val,
            self.binders_passed,
            val.has_escaping_bound_vars()
        );

        if self.binders_passed == 0 || !val.has_escaping_bound_vars() {
            return val;
        }

        let result = ty::fold::shift_vars(TypeFolder::tcx(self), val, self.binders_passed);
        debug!("shift_vars: shifted result = {:?}", result);

        result
    }

    fn shift_region_through_binders(&self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if self.binders_passed == 0 || !region.has_escaping_bound_vars() {
            return region;
        }
        ty::fold::shift_region(self.tcx, region, self.binders_passed)
    }
}




#[derive(PartialEq, Eq, Hash, Debug)]
struct VirtualCallee<'tcx> {
    trait_id: DefId,
    trait_fn: DefId,
    substs: SubstsRef<'tcx>,
}



#[derive(Debug)]
struct VirtualCallContext<'tcx> {
    call_sites: HashSet<CallSite>,
    processed_adt_substs: HashSet<(DefId, SubstsRef<'tcx>)>,
}

impl<'tcx> VirtualCallContext<'tcx> {
    pub fn add_call_site(&mut self, call_site: CallSite) {
        self.call_sites.insert(call_site);
    }

    pub fn get_call_sites(&self) -> impl Iterator<Item = &CallSite> {
        self.call_sites.iter()
    }

    pub fn add_processed_adt_substs(&mut self, adt_id: DefId, substs: SubstsRef<'tcx>) {
        self.processed_adt_substs.insert((adt_id, substs));
    }

    pub fn is_processed_adt_substs(&self, adt_id: DefId, substs: SubstsRef<'tcx>) -> bool {
        self.processed_adt_substs.contains(&(adt_id, substs))
    }
}

//let subst = Substs::build_for_def(tcx, generics, &[]);
//static Substs: SubstsRef<'static> = &Substs::build_for_def(tcx, generics, &[]);

//pub trait AsGlobalCtxt<'tcx>: AsRef<GlobalCtxt<'tcx>> {}

//impl<'tcx, T: AsRef<GlobalCtxt<'tcx>>> AsGlobalCtxt<'tcx> for T {}

//impl<'tcx> AsRef<GlobalCtxt<'tcx>> for TyCtxtObject<'tcx> {
//    fn as_ref(&self) -> &GlobalCtxt<'tcx> {
//     self.global_tcx()
//    }
//}
// fn enter<'tcx, F, R>(&'tcx GlobalCtxt<'tcx> gl, f: F) -> R
//     where
//         F: FnOnce(TyCtxt<'tcx>) -> R,
//     {
//         let icx = tls::ImplicitCtxt::new(gl);
//         tls::enter_context(&icx, || f(icx.tcx))
//     }



//FnOnce
#[feature(unboxed_closures)]
//impl<'tcx, R:FnOnce> VirtualCallee<'tcx> {
impl<'tcx> VirtualCallee<'tcx> {

    // fn enter< F, R>(& GlobalCtxt<'tcx> gl, f: F) -> R
    // where
    //     F: FnOnce(TyCtxt<'tcx>) -> R,
    // {
    //     let icx = tls::ImplicitCtxt::new(gl);
    //     tls::enter_context(&icx, || f(icx.tcx))
    // }

    fn probe_possible_callees(
        &self,
        tcx: TyCtxt<'tcx>,
        substs_infos: &HashMap<DefId, HashSet<SubstsRef<'tcx>>>,
        context: &mut VirtualCallContext<'tcx>,
    ) -> Vec<Method<'tcx>> {
        let mut candidates = vec![];
        // Returns an iterator containing all impls.
        for impl_id in tcx.all_impls(self.trait_id) {
            let impl_kind = tcx.type_of(impl_id).kind();
            match impl_kind {
                TyKind::Adt(adt_def, adt_substs) => {
                    let adt_id = adt_def.did();
                    let substs_set = substs_infos.get(&adt_id);
                    if substs_set.is_none() {
                        continue;
                    }

                    let substs_set = substs_set.unwrap();
                    for substs in substs_set {
                        if context.is_processed_adt_substs(adt_id, substs) {
                            continue;
                        }

                        let mut generics_arg_map = HashMap::new();
                        let mut concrete_generic_arg_mismatched = false;
                        for (adt_generic_ty, actual_ty) in adt_substs.iter().zip(substs.iter()) {
                            let ty = adt_generic_ty.expect_ty();
                            match ty.kind() {
                                TyKind::Param(param_ty) => {
                                    let index = param_ty.index;
                                    generics_arg_map.insert(index, actual_ty);
                                }
                                other => {
                                    if utils::is_concrete(other) {
                                        if adt_generic_ty != actual_ty {
                                            concrete_generic_arg_mismatched = true;
                                            break;
                                        }
                                    } else {
                                        todo!("unknown type of ADT generic parameter: {:?}", other);
                                    }
                                }
                            }
                        }

                        if concrete_generic_arg_mismatched {
                            context.add_processed_adt_substs(adt_id, substs);
                            continue;
                        }

                        let param_env = ParamEnv::reveal_all();
                        let rebased_substs =
                            InternalSubsts::for_item(tcx, impl_id, |param_def, _| {
                                let index = param_def.index;
                                if let Some(ty) = generics_arg_map.get(&index) {
                                    *ty
                                } else {
                                    tcx.mk_param_from_def(param_def)
                                }
                            });
                        let impl_trait_ref = tcx.impl_trait_ref(impl_id).unwrap();
                        //let gcx_ref: &GlobalCtxt<'tcx> = tcx.gcx;


                        //tcx.as_ref().enter(|infcx| {             // cannot modify 01
                        // (*tcx).enter(|tcx| {
                        //tcx.clone().enter(|infcx| {



                            // fn enter<'tcx, F, R>(&'tcx GlobalCtxt<'tcx> gl, f: F) -> R
                            // where
                            //     F: FnOnce(TyCtxt<'tcx>) -> R,
                            // {
                            //     let icx = tls::ImplicitCtxt::new(gl);
                            //     tls::enter_context(&icx, || f(icx.tcx))
                            // }

                        //定义了一个名为 enter_fn 的闭包，它接受两个参数：一个 GlobalCtxt 的引用和一个函数 f。
                        //这个闭包创建了一个 ImplicitCtxt，然后使用 tls::enter_context 函数在 ImplicitCtxt 的上下文中调用函数 f
                        // let enter_fn = |t_tcx: &GlobalCtxt<'tcx>, f|{
                        //         //
                        //         let icx = tls::ImplicitCtxt::new(t_tcx);
                        //         tls::enter_context(&icx, || f(icx.tcx))
                        // };
                        // let icx_temp = tls::ImplicitCtxt::new( *tcx );
                        // let tcx_temp = icx_temp.tcx;

                        //tcx.infer_ctxt().enter(|infcx| // tcx TyCtxt, infer_ctxt ,enter(||),infcx InferCtxt,
                        let mut enter_func =||{//ImplicitCtxt
                                let infcx = tcx.infer_ctxt().build();
                                let mut fulfill_cx = <dyn TraitEngine<'tcx>>::new(infcx.tcx);  // cannot modify 02 ???
                                //let mut fulfill_cx = rustc_trait_selection::traits::FulfillmentContext::new();  //modify:
                                let revised_impl_trait_substs = impl_trait_ref
                                    .substs
                                    .iter()
                                    .take(1)
                                    .chain(self.substs.iter().skip(1))
                                    .collect::<Vec<_>>();

                                let trait_ref = TraitRef::from_method(
                                    tcx,
                                    self.trait_id,
                                    tcx.intern_substs(&revised_impl_trait_substs),
                                );
                                let trait_predicate: Predicate<'tcx> = Clause::Trait(
                                    TraitPredicate{
                                        trait_ref,
                                        polarity: rustc_middle::ty::ImplPolarity::Positive,
                                        constness: rustc_middle::ty::BoundConstness::NotConst,
                                    }
                                ).to_predicate(tcx);
                             
                            //     let clause_trait = Clause::Trait( //modify 04
                            //    // let trait_predicate = PredicateKind::Trait(
                            //         //TraitPredicate { trait_ref },       //modify 03
                            //         TraitPredicate
                            //         {
                            //             trait_ref,
                            //             polarity: rustc_middle::ty::ImplPolarity::Positive,
                            //             constness: rustc_middle::ty::BoundConstness::NotConst,
                            //         }

                            //         /*TraitPredicate {
                            //             trait_ref,
                            //             polarity:hir::TraitBoundModifier::None,
                            //             constness: hir::Constness::NotConst,
                            //         },*/
                            //         // A const trait bound looks like:
                            //         // ```
                            //         // struct Foo<Bar> where Bar: const Baz { ... }
                            //         // ```
                            //         // For now we don't take this situation into consideration.
                            //         // Constness::NotConst,           //modify 03
                            //     );
                            //     // clause_trait.abcd();
                            //     let trait_predicate: Predicate<'tcx> = clause_trait.to_predicate(tcx);
                                /*
                                1. change rust version to nightly-2021-06-23, 
                                2. basing on the func, create the doc of 21-6-23.
                                3. find the source code of   rustc_middle ,  Predicate<'tcx>.subst(,), learn about what it 's doing.  InferCtxt, 
                                _. get 23-1-3 Predicate<'tcx> 's doc.(*)
                                
                                4. use *'s [func]s to impl a new subst func to get the same result of the older one.
                                
                                
                                 */
                                //k2mistake
                                //代码中的 TyCtxt<'_'> 应该是一个类型注释，用于指定 Obligation 对象的类型。
                                //但是这里似乎有一个错误，应该传递一个 TyCtxt 类型的实例作为参数，而不是类型注释。
                                let mut folder = SubstFolder { tcx, substs: rebased_substs, binders_passed: 0 };// TODO*: find or write(create) a Folder struct to substitute the SubstFolder,
                                let fold_result = trait_predicate.try_fold_with(&mut folder);
                                if let Result::Ok(trait_predicate) = fold_result{
                                    // let trait_predicate = trait_predicate.subst(tcx, rebased_substs);// 
                                    let obligation = Obligation::new(
                                    //TyCtxt<'_'>,
                                        tcx,
                                        ObligationCause::dummy(),
                                        param_env,
                                        trait_predicate,
                                    );
                                    fulfill_cx.register_predicate_obligation(&infcx, obligation.clone());
                                    // Drives compiler to do type checking and constraint solving.
                                    //Vec<FulfillmentError<'tcx>, Global>
                                    let fullfillcx_errs = fulfill_cx.select_all_or_error(&infcx);//
    
                                    if fullfillcx_errs.len()>0 {   //modify 05
                                        //let errors: Vec<_> = err.into_iter().collect();
    
                                        debug!(
                                            "candidate selecting failed: `{:?}` doesn't implements `{:?}`, due to `{:?}`",
                                            trait_ref.substs, trait_ref.def_id, fullfillcx_errs[0] //
                                        );
                                    } else {
                                        let predicates = tcx.predicates_of(impl_id);
                                        predicates.predicates.iter().for_each(|(predicate, _)| {
                                            let kind = predicate.kind().skip_binder();
                                            match kind {
                                                // Clause::Trait(..) | Clause::Projection(..) => (),   ///modify 06
                                                //PredicateKind::Trait(..) | PredicateKind::Projection(..) => (),
                                                PredicateKind::Clause(Clause::Trait(..)) | PredicateKind::Clause(Clause::Projection(..)) => (),
                                                unknown => todo!("unknown predicate kind `{:?}`", unknown),
                                            }
                                        });
    
                                        let assoc_items = tcx.associated_items(impl_id);
                                        let target_name = tcx.item_name(self.trait_fn);
                                        let mut assoc_fn = assoc_items.in_definition_order().filter_map(|assoc_item| {
                                            if assoc_item.kind == AssocKind::Fn && assoc_item.ident(tcx).name == target_name {
                                                Some(assoc_item.def_id)
                                            } else {
                                                None
                                            }
                                        });
    
                                        let instantiate_substs = Self::instantiate_proj_substs(
                                            tcx,
                                            predicates,
                                            rebased_substs,
                                            param_env,
                                            &mut fulfill_cx,
                                            &infcx,
                                        );
    
                                        if let Some(def_id) = assoc_fn.next() {
                                            // In Rust, `Clone` trait is not object-safe because the
                                            // signature of its clone method returns `Self`, so we are
                                            // very sure that it cannot be used in trait object.
                                            candidates.push(Method {
                                                def_id,
                                                substs: tcx.mk_substs(instantiate_substs.iter()),
                                                self_ty: None,
                                                used_for_clone: false,
                                            })
                                        } else {
                                            todo!("default impl");
                                        }
                                        context.add_processed_adt_substs(adt_id, substs);
                                    }
                                
                                }else if let Result::Err(err) = fold_result  {
                                    // let err = fold_result.0;
                                    println!("In analyzer/control_flow/builder.rs:350, result not matched");
                                    println!("{}",err);
                                }

                                

                                //let trait_predicate = trait_predicate.subst(tcx, rebased_substs);
                                //let obligation_predicate = ObligationPredicate::Trait(trait_predicate);
                                // let obligation = Obligation::new(
                                //     ObligationCause::dummy(),
                                //    param_env,
                                //    obligation_predicate,
                                // );

                              
                        };
                        enter_func();
                    }
                }
                _ => todo!("unknown impl kind: {:?}", impl_kind),
            }
        }
        candidates
    }

    fn instantiate_proj_substs(
        tcx: TyCtxt<'tcx>,
        predicates: GenericPredicates<'tcx>,
        substs: SubstsRef<'tcx>,
        param_env: ParamEnv<'tcx>,
        fulfill_cx: &mut std::boxed::Box<dyn TraitEngine<'tcx>>,// 
        //infcx: &InferCtxt<'_, 'tcx>,
        infcx: &InferCtxt<'tcx>,
    ) -> Vec<GenericArg<'tcx>> {
        let mut instantiated_substs = Vec::from_iter(substs);
        loop {
            let predicates = predicates
                .instantiate_own(tcx, tcx.mk_substs(instantiated_substs.iter()))
                .predicates;

            let mut substituted = false;
            for predicate in predicates {
                //if let PredicateKind::Projection(..) = predicate.kind().skip_binder() {   // modify 07  cannot modify
                if let rustc_middle::ty::PredicateKind::Clause(Clause::Projection(..)) =
                    predicate.kind().skip_binder()
                {
                    //if let Clause::Projection(..) = predicate.kind().skip_binder() {

                    //if let AliasKind::Projection(..) = predicate.kind().skip_binder() { Clause::Projection
                    let obligation =
                        Obligation::new(tcx, ObligationCause::dummy(), param_env, predicate);
                    fulfill_cx.register_predicate_obligation(&infcx, obligation);
                    let errors = fulfill_cx.select_all_or_error(&infcx); //Vec<rustc_trait_selection::traits::FulfillmentError<'_>>
                    if errors.len() > 0 {
                        // modify 08 cannot modify    -----------------------
                        debug_assert!(errors.len() == 1);
                        let code = &errors[0].code;
                        if let FulfillmentErrorCode::CodeProjectionError(mismatched_proj) = code {
                            if let TypeError::Sorts(expected_found) = mismatched_proj.err {
                                let generic_arg = GenericArg::from(expected_found.expected);

                                for item in instantiated_substs.iter_mut() {
                                    substituted = true;
                                    if item.expect_ty() == expected_found.found {
                                        *item = generic_arg;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if !substituted {
                break;
            }
        }
        instantiated_substs
    }
}

pub struct Builder<'graph, 'tcx> {
    cfg: &'graph mut ForwardCFG<'tcx>,
    tcx: TyCtxt<'tcx>,
    work_list: LinkedList<Method<'tcx>>,
    substs_cache: HashMap<DefId, HashSet<SubstsRef<'tcx>>>,
    virtual_callees: HashMap<VirtualCallee<'tcx>, VirtualCallContext<'tcx>>,
    call_site_cache: HashMap<CallSite, HashSet<Method<'tcx>>>,
}

impl<'graph, 'tcx> Builder<'graph, 'tcx> {
    pub fn new(cfg: &'graph mut ForwardCFG<'tcx>) -> Self {
        let tcx = cfg.tcx;
        Self {
            cfg,
            tcx,
            work_list: Default::default(),
            substs_cache: Default::default(),
            virtual_callees: Default::default(),
            call_site_cache: Default::default(),
        }
    }

    pub fn build<'a>(&mut self, entry_points: &[&DefId]) {
        let empty_substs = self.tcx.intern_substs(&[]);
        let entry_points = entry_points
            .iter()
            .map(|def_id| Method {
                def_id: **def_id,
                substs: empty_substs,
                self_ty: None,
                used_for_clone: false,
            })
            .collect::<Vec<_>>();
        for entry_point in &entry_points {
            self.insert_task(*entry_point, None);
        }

        loop {
            if let Some(method) = self.work_list.pop_front() {
                if let Some(cause) = utils::is_special_method(self.tcx, method.def_id) {
                    debug!(
                        "encounter special method `{:?}` due to `{:?}`, skip processing",
                        method, cause
                    );
                    if self.cfg.methods.iter().all(|m| m != &method) {
                        self.cfg.methods.push(method);
                    }
                    continue;
                }
                if self.cfg.methods.iter().all(|m| m != &method) {
                    debug!("process method {:?}", method);
                    let def_id = method.def_id;
                    let body = self.tcx.optimized_mir(def_id);
                    self.visit_body(method, body);
                    self.cfg.methods.push(method);
                }
            } else {
                let mut no_new_callee_found = true;
                let mut new_tasks = vec![];
                for (callee, context) in self.virtual_callees.iter_mut() {
                    debug!("iter virtual_callees {:?} {:?}", callee, context);
                    let possible_callees =
                        callee.probe_possible_callees(self.tcx, &self.substs_cache, context);

                    if !possible_callees.is_empty() {
                        no_new_callee_found = false;
                    }

                    debug!(
                        "for virtual call `{:?}` found possible callees: {:?}",
                        callee, possible_callees
                    );
                    for call_site in context.get_call_sites() {
                        for possible_callee in &possible_callees {
                            let possible_callee = *possible_callee;
                            new_tasks.push((possible_callee, *call_site));
                        }
                    }
                }

                if no_new_callee_found {
                    break;
                } else {
                    for task in new_tasks {
                        self.insert_task(task.0, Some(task.1));
                    }
                }
            }
        }

        debug_assert!(self.cfg.start_point.is_empty());
        debug_assert!(self.cfg.end_points.is_empty());
        debug_assert!(self.cfg.node_to_index.is_empty());

        let methods = self.cfg.methods.clone();

        // Phase I: adds normal edges between basic blocks containing no `Call` terminator.
        for (method_index, method) in methods.iter().enumerate() {
            let def_id = method.def_id;
            let cause = utils::is_special_method(self.tcx, def_id);
            if cause.is_some() {
                let fake_node = Node {
                    basic_block: Some(START_BLOCK),
                    belongs_to: method_index,
                    kind: NodeKind::Fake(cause.unwrap()),
                };
                if let Some(index) = self.cfg.node_to_index.get(&fake_node) {
                    *index
                } else {
                    let index = self.cfg.add_node(fake_node);
                    self.cfg.node_to_index.insert(fake_node, index);
                    index
                };
                continue;
            }

            let body = self.tcx.optimized_mir(def_id);
            let basic_blocks = &body.basic_blocks;
            let mut bb_to_index = HashMap::new();
            let normal_edge = Edge {
                container: Some(*method),
                kind: EdgeKind::Normal,
                is_certain: true,
            };

            for bb in basic_blocks.indices() {
                let node = Node {
                    basic_block: Some(bb),
                    belongs_to: method_index,
                    kind: NodeKind::Normal,
                };
                let node_index = if let Some(index) = self.cfg.node_to_index.get(&node) {
                    *index
                } else {
                    let index = self.cfg.add_node(node);
                    self.cfg.node_to_index.insert(node, index);
                    index
                };

                if bb == START_BLOCK {
                    let start_node = Node {
                        basic_block: None,
                        belongs_to: method_index,
                        kind: NodeKind::Start,
                    };
                    let start_node_index = self.cfg.add_node(start_node);
                    self.cfg.node_to_index.insert(start_node, start_node_index);
                    self.cfg.add_edge(start_node_index, node_index, normal_edge);
                    self.cfg.start_point.insert(method_index, start_node_index);
                }
                bb_to_index.insert(bb, node_index);
            }

            for bb in basic_blocks.indices() {
                let BasicBlockData { ref terminator, .. } = basic_blocks[bb];
                if let Some(terminator) = terminator {
                    let cfg = &mut self.cfg;
                    let mut add_edge =
                        |from, to, edge| cfg.add_edge(bb_to_index[&from], bb_to_index[to], edge);

                    match &terminator.kind {
                        TerminatorKind::Goto { target } => add_edge(bb, target, normal_edge),
                        TerminatorKind::SwitchInt { targets, .. } => {
                            let all_targets = targets.all_targets();
                            for target in all_targets {
                                add_edge(bb, target, normal_edge)
                            }
                        }
                        TerminatorKind::Drop { target, unwind, .. }
                        | TerminatorKind::DropAndReplace { target, unwind, .. } => {
                            add_edge(bb, target, normal_edge);
                            if let Some(unwind) = unwind {
                                add_edge(bb, unwind, normal_edge)
                            }
                        }
                        TerminatorKind::Assert {
                            target, cleanup, ..
                        } => {
                            add_edge(bb, target, normal_edge);
                            if let Some(cleanup) = cleanup {
                                add_edge(bb, cleanup, normal_edge)
                            }
                        }
                        TerminatorKind::Yield { resume, drop, .. } => {
                            add_edge(bb, resume, normal_edge);
                            if let Some(cleanup) = drop {
                                add_edge(bb, cleanup, normal_edge)
                            }
                        }
                        TerminatorKind::FalseEdge { real_target, .. }
                        | TerminatorKind::FalseUnwind { real_target, .. } => {
                            add_edge(bb, real_target, normal_edge);
                        }
                        TerminatorKind::InlineAsm { destination, .. } => {
                            if let Some(dest) = destination {
                                add_edge(bb, dest, normal_edge);
                            }
                        }
                        TerminatorKind::Return
                        | TerminatorKind::Resume
                        | TerminatorKind::Abort
                        | TerminatorKind::Unreachable => {
                            let node_index = bb_to_index[&bb];
                            let end_node = Node {
                                basic_block: None,
                                belongs_to: method_index,
                                kind: NodeKind::End,
                            };
                            let end_node_index = self.cfg.add_node(end_node);
                            self.cfg.node_to_index.insert(end_node, end_node_index);
                            self.cfg.add_edge(node_index, end_node_index, normal_edge);

                            self.cfg
                                .end_points
                                .entry(method_index)
                                .or_insert(vec![])
                                .push(end_node_index);
                        }
                        _ => (),
                    }
                }
            }
        }

        // Phase II: adds call and call-to-return edges for all call sites.
        for (method_index, method) in methods.iter().enumerate() {
            let def_id = method.def_id;
            if utils::is_special_method(self.tcx, def_id).is_some() {
                continue;
            }

            let body = self.tcx.optimized_mir(def_id);
            let basic_blocks = &body.basic_blocks;
            for bb in basic_blocks.indices() {
                let BasicBlockData { ref terminator, .. } = basic_blocks[bb];
                if let Some(terminator) = terminator {
                    match terminator.kind {
                        TerminatorKind::Call {
                            destination,
                            target,
                            cleanup,
                            ..
                        } => {
                            let call_site = CallSite {
                                caller: method_index,
                                bb_id: bb.index(),
                            };
                            let callees = self.call_site_cache.get(&call_site);
                            debug_assert!(
                                callees.is_some(),
                                "{:?} {:?}",
                                self.cfg.get_method_by_index(call_site.caller).def_id,
                                call_site.bb_id,
                            );
                            let callees = callees.unwrap();
                            debug_assert!(!callees.is_empty());
                            let is_certain = callees.len() == 1;

                            let prev_node = Node {
                                basic_block: Some(bb),
                                belongs_to: method_index,
                                kind: NodeKind::Normal,
                            };
                            let curr_node = Node {
                                basic_block: Some(bb),
                                belongs_to: method_index,
                                kind: NodeKind::Call,
                            };
                            let curr_node_index = self.cfg.add_node(curr_node);
                            self.cfg.add_edge(
                                self.cfg.node_to_index[&prev_node],
                                curr_node_index,
                                Edge {
                                    container: Some(*method),
                                    kind: EdgeKind::Normal,
                                    is_certain: true,
                                },
                            );
                            self.cfg.node_to_index.insert(curr_node, curr_node_index);

                            let call_to_return_edge = Edge {
                                container: Some(*method),
                                kind: EdgeKind::CallToReturn,
                                is_certain: true,
                            };

                            if let Some(dest) = target {
                                // Option<_,_>     // modify 09 cannot sure // destination -> target
                                let dest_index = self.cfg.node_to_index[&Node {
                                    basic_block: Some(dest),
                                    belongs_to: method_index,
                                    kind: NodeKind::Normal,
                                }];
                                self.cfg
                                    .add_edge(curr_node_index, dest_index, call_to_return_edge);
                            }

                            if let Some(cleanup) = cleanup {
                                let cleanup_index = self.cfg.node_to_index[&Node {
                                    basic_block: Some(cleanup),
                                    belongs_to: method_index,
                                    kind: NodeKind::Normal,
                                }];
                                self.cfg.add_edge(
                                    curr_node_index,
                                    cleanup_index,
                                    call_to_return_edge,
                                )
                            }

                            for callee in callees {
                                let cause = utils::is_special_method(self.tcx, callee.def_id);
                                if cause.is_some() {
                                    let callee_index = self
                                        .cfg
                                        .methods
                                        .iter()
                                        .position(|method| method == callee)
                                        .unwrap();
                                    let fake_node = Node {
                                        basic_block: Some(START_BLOCK),
                                        belongs_to: callee_index,
                                        kind: NodeKind::Fake(cause.unwrap()),
                                    };

                                    self.cfg.add_edge(
                                        curr_node_index,
                                        self.cfg.node_to_index[&fake_node],
                                        Edge {
                                            container: None,
                                            kind: EdgeKind::Call,
                                            is_certain: true,
                                        },
                                    );

                                    let successors = terminator.kind.successors();
                                    for successor in successors {
                                        let succ_node = Node {
                                            //basic_block: Some(*successor),      // modify 10 cannot modify
                                            basic_block: Some(successor),
                                            belongs_to: method_index,
                                            kind: NodeKind::Normal,
                                        };
                                        self.cfg.add_edge(
                                            self.cfg.node_to_index[&fake_node],
                                            self.cfg.node_to_index[&succ_node],
                                            Edge {
                                                container: None,
                                                kind: EdgeKind::Return,
                                                is_certain: true,
                                            },
                                        );
                                    }
                                    continue;
                                }

                                let callee_index = self
                                    .cfg
                                    .methods
                                    .iter()
                                    .position(|method| method == callee)
                                    .unwrap();
                                let callee_start_point = self.cfg.start_point[&callee_index];
                                self.cfg.add_edge(
                                    curr_node_index,
                                    callee_start_point,
                                    Edge {
                                        container: None,
                                        kind: EdgeKind::Call,
                                        is_certain,
                                    },
                                );

                                let end_points = self.cfg.end_points[&callee_index].clone();
                                let successors = terminator.kind.successors();

                                for successor in successors {
                                    let succ_node = Node {
                                        basic_block: Some(successor), // modify 11 cannot modify   same as 10
                                        belongs_to: method_index,
                                        kind: NodeKind::Normal,
                                    };
                                    for end_point in &end_points {
                                        self.cfg.add_edge(
                                            *end_point,
                                            self.cfg.node_to_index[&succ_node],
                                            Edge {
                                                container: None,
                                                kind: EdgeKind::Return,
                                                is_certain: true,
                                            },
                                        );
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
        }

        debug!("all nodes in cfg:");
        for node in self.cfg.graph.raw_nodes().iter() {
            let node = &node.weight;
            debug!(
                "belongs_to: {:?}, basic_block: {:?}, kind: {:?}",
                self.cfg.get_method_by_index(node.belongs_to).def_id,
                node.basic_block,
                node.kind,
            );
        }

        debug!("all edges in cfg:");
        for edge in self.cfg.graph.raw_edges().iter() {
            let src = edge.source();
            let tgt = edge.target();
            let src_weight = self.cfg.graph.node_weight(src).unwrap();
            let tgt_weight = self.cfg.graph.node_weight(tgt).unwrap();
            let edge_weight = edge.weight;
            debug!(
                "{:?}({:?}) -> {:?}({:?}): {:?}",
                self.cfg.get_method_by_index(src_weight.belongs_to).def_id,
                src_weight.basic_block,
                self.cfg.get_method_by_index(tgt_weight.belongs_to).def_id,
                tgt_weight.basic_block,
                edge_weight.kind
            );
        }

        debug!("all methods in cfg:");
        for (index, method) in self.cfg.methods.iter().enumerate() {
            debug!("index: {:?}, method: `{:?}`", index, method);
        }
    }

    fn visit_body(&mut self, method: Method<'tcx>, body: &'tcx Body<'tcx>) {
        let local_decls = &body.local_decls;
        for local_decl in local_decls {
            let local_ty = local_decl.ty;
            match local_ty.kind() {
                TyKind::Adt(adt_def, substs) => {
                    let map =
                        utils::generate_generic_args_map(self.tcx, method.def_id, method.substs);
                    let substs = utils::specialize_substs(self.tcx, substs, &map);
                    self.substs_cache
                        .entry(adt_def.did())
                        .or_default()
                        .insert(substs);
                }
                _ => (),
            }
        }

        let lang_items = self.tcx.lang_items();
        let clone_trait = lang_items.clone_trait();

        for bb in body.basic_blocks.indices() {
            let BasicBlockData { ref terminator, .. } = body[bb];

            if let Some(terminator) = terminator {
                let Terminator { kind, .. } = terminator;
                if let TerminatorKind::Call { func, args, .. } = kind {
                    let bb_id = bb.index();
                    let call_kind = func.ty(local_decls, self.tcx).kind();

                    match call_kind {
                        TyKind::FnDef(def_id, substs) => {
                            let trait_id = self.tcx.trait_of_item(*def_id);
                            let used_for_clone = trait_id == clone_trait;
                            let callee = Method {
                                def_id: *def_id,
                                substs,
                                self_ty: None,
                                used_for_clone,
                            };
                            self.visit_call(method, callee, args, bb_id);
                        }
                        unknown => todo!("unknown kind of invocation: {:?}", unknown),
                    }
                }
            }
        }
    }

    fn visit_call(
        &mut self,
        caller: Method<'tcx>,
        callee: Method<'tcx>,
        args: &[mir::Operand<'tcx>],
        bb_id: usize,
    ) {
        let caller_index = self.cfg.methods.len();
        let call_site = CallSite {
            caller: caller_index,
            bb_id,
        };
        match self.resolve(caller, callee, args) {
            Left(callee) => {
                self.insert_task(callee, Some(call_site));
            }
            Right(virtual_callee) => {
                self.virtual_callees
                    .entry(virtual_callee)
                    .or_insert(VirtualCallContext {
                        call_sites: HashSet::from_iter([call_site]),
                        processed_adt_substs: Default::default(),
                    })
                    .add_call_site(call_site);
            }
        }
    }

    fn insert_task(&mut self, mut callee: Method<'tcx>, call_site: Option<CallSite>) {
        let impl_id = self.tcx.impl_of_method(callee.def_id);
        if let Some(impl_id) = impl_id {
            let impl_ty = self.tcx.type_of(impl_id);
            let impl_kind = impl_ty.kind();
            match impl_kind {
                TyKind::Adt(adt_def, substs) => {
                    let substs = self.tcx.mk_substs(substs.iter().map(|generic_arg| {
                        let generic_arg_kind = generic_arg.unpack();
                        if let GenericArgKind::Type(ty) = generic_arg_kind {
                            if let TyKind::Param(param_ty) = ty.kind() {
                                let index = param_ty.index;
                                *callee.substs.get(index as usize).unwrap()
                            } else {
                                generic_arg
                            }
                        } else {
                            generic_arg
                        }
                    }));
                    callee.self_ty = Some(self.tcx.mk_adt(*adt_def, substs));
                }
                TyKind::Param(param_ty) => {
                    let index = param_ty.index;
                    callee.self_ty = Some(callee.substs[index as usize].expect_ty());
                }
                TyKind::Ref(region, ty, mutbl) => {
                    if let TyKind::Param(param_ty) = ty.kind() {
                        let index = param_ty.index;
                        callee.self_ty = Some(self.tcx.mk_ref(
                            *region,
                            TypeAndMut {
                                ty: callee.substs[index as usize].expect_ty(),
                                mutbl: *mutbl,
                            },
                        ));
                    } else if utils::is_concrete(ty.kind()) {
                        callee.self_ty = Some(impl_ty);
                    } else {
                        todo!(
                            "encounter unknown self type `{:?}` for `{:?}`",
                            impl_kind,
                            callee.def_id,
                        );
                    }
                }
                ty if utils::is_concrete(ty) => {
                    callee.self_ty = Some(impl_ty);
                }
                _ => todo!(
                    "encounter unknown self type `{:?}` for `{:?}`",
                    impl_kind,
                    callee.def_id,
                ),
            }
        }

        if let Some(call_site) = call_site {
            self.call_site_cache
                .entry(call_site)
                .or_default()
                .insert(callee);
        }

        if !self.cfg.methods.iter().any(|method| method == &callee) {
            self.work_list.push_back(callee);
        }
    }

    fn resolve(
        &mut self,
        caller: Method<'tcx>,
        callee: Method<'tcx>,
        args: &[mir::Operand<'tcx>],
    ) -> Either<Method<'tcx>, VirtualCallee<'tcx>> {
        if matches!(
            KnownNames::get(self.tcx, callee.def_id),
            KnownNames::CoreOpsFunctionFnCall
                | KnownNames::CoreOpsFunctionFnCallMut
                | KnownNames::CoreOpsFunctionFnOnceCallOnce
        ) {
            let target = &args[0];
            match target {
                mir::Operand::Move(..) => {
                    let map =
                        utils::generate_generic_args_map(self.tcx, caller.def_id, caller.substs);
                    let callee_substs = utils::specialize_substs(self.tcx, callee.substs, &map);
                    let ty = callee_substs[0].expect_ty();
                    match ty.kind() {
                        TyKind::Closure(callee_id, callee_substs)
                        | TyKind::FnDef(callee_id, callee_substs) => {
                            let actual_callee = Method {
                                def_id: *callee_id,
                                substs: callee_substs,
                                self_ty: None,
                                used_for_clone: false,
                            };
                            return Left(actual_callee);
                        }
                        unknown => todo!("unknown kind of indirect invocation: {:?}", unknown),
                    }
                }
                unknown => todo!("unknown target of indirect invocation: {:?}", unknown),
            }
        }

        let param_env = ParamEnv::reveal_all();
        let map = utils::generate_generic_args_map(self.tcx, caller.def_id, caller.substs);
        let callee_substs = utils::specialize_substs(self.tcx, callee.substs, &map);
        if let Ok(Some(instance)) =
            Instance::resolve(self.tcx, param_env, callee.def_id, callee_substs)
        {
            match instance.def {
                InstanceDef::Virtual(trait_fn, ..) => {
                    let trait_id = self.tcx.trait_of_item(trait_fn).unwrap();
                    let substs = self.tcx.intern_substs(&instance.substs[..]);
                    let virtual_call = VirtualCallee {
                        trait_id,
                        trait_fn,
                        substs,
                    };
                    return Right(virtual_call);
                }
                _ => {
                    let substs = utils::specialize_substs(self.tcx, instance.substs, &map);
                    return Left(Method {
                        def_id: instance.def_id(),
                        substs,
                        self_ty: None,
                        used_for_clone: callee.used_for_clone,
                    });
                }
            }
        } else {
            todo!(
                "unable to resolve callee `{:?}` with substs `{:?}`",
                callee.def_id,
                callee.substs,
            );
        }
    }
}
