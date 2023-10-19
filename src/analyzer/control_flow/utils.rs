use crate::known_names::KnownNames;
use anyhow::__private::kind::AdhocKind;
use log::*;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::AliasKind;
use rustc_middle::ty::{
    subst::{GenericArg, GenericArgKind, InternalSubsts, SubstsRef},
    Const, ConstKind, DefIdTree, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef,
    FnSig, ParamTy, Projection, Ty, TyCtxt, TyKind, TypeAndMut,
};
use rustc_span::Symbol;
use std::collections::HashMap;
use rustc_middle::ty::Clause;
use rustc_middle::ty::ProjectionPredicate;

pub fn is_concrete(ty: &TyKind<'_>) -> bool {
    match ty {
        TyKind::Adt(_, gen_args)
        | TyKind::FnDef(_, gen_args)                      
        | TyKind::Closure(_, gen_args)              
        | TyKind::Generator(_, gen_args, _)   => are_concrete(gen_args), // modify 14-1 cannot modify  ---- no current match variant                                   
        //| TyKind::Tuple(gen_args) => are_concrete(gen_args),  //genju are_concrete gai gen_args de leixing subsets he list  //fanxing // ruhe shi jiuzhaozhe 
        TyKind::Alias(alias_kind, alias_ty) => are_concrete(alias_ty.substs),
        TyKind::Tuple(list_ty)=>are_concrete(list_ty.as_substs()),
        TyKind::Bound(..)                    
        | TyKind::Dynamic(..)                
        | TyKind::Error(..)                  
        | TyKind::Infer(..)                  
        | TyKind::Param(..) => false,                 
        TyKind::Ref(_, ty, _) => is_concrete(ty.kind()),                  
        _ => true,
    }
}



pub fn are_concrete(gen_args: SubstsRef<'_>) -> bool {
    for gen_arg in gen_args.iter() {
        if let GenericArgKind::Type(ty) = gen_arg.unpack() {
            if !is_concrete(ty.kind()) {
                return false;
            }
        }
    }
    true
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum SpecialCause {
    NoMir,
    Predefined,
}

pub fn is_special_method<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<SpecialCause> {
    let known_name = KnownNames::get(tcx, def_id);
    if !matches!(
        known_name,
        KnownNames::CoreOpsFunctionFnCall
            | KnownNames::CoreOpsFunctionFnCallMut
            | KnownNames::CoreOpsFunctionFnOnceCallOnce
            | KnownNames::None,
    ) {
        return Some(SpecialCause::Predefined);
    }
    if !tcx.is_mir_available(def_id) {
        Some(SpecialCause::NoMir)
    } else {
        None
    }
}

pub fn generate_generic_args_map<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> HashMap<Symbol, GenericArg<'tcx>> {
    let mut map = HashMap::new();
    InternalSubsts::for_item(tcx, def_id, |param_def, _| {
        if let Some(generic_arg) = substs.get(param_def.index as usize) {
            map.insert(param_def.name, *generic_arg);
        } else {
            todo!("unmapped generic param definition: {:?}", param_def);
        }
        tcx.mk_param_from_def(param_def)
    });
    map
}

pub fn specialize_substs<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: &[GenericArg<'tcx>],
    generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
) -> SubstsRef<'tcx> {
    let specialized_generic_args = substs
        .iter()
        .map(|generic_arg| specialize_generic_arg(tcx, &generic_arg, generic_args_map))
        .collect::<Vec<_>>();
    tcx.intern_substs(&specialized_generic_args)
}

fn specialize_generic_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic_arg: &GenericArg<'tcx>,
    generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
) -> GenericArg<'tcx> {
    match generic_arg.unpack() {
        GenericArgKind::Type(ty) => specialize_type_generic_arg(tcx, ty, generic_args_map).into(),
        GenericArgKind::Const(constant) => {
            specialize_const_generic_arg(constant, generic_args_map).into() // ???  
        }
        _ => *generic_arg,
    }
}

pub fn specialize_type_generic_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    generic_args_map: &HashMap<rustc_span::Symbol, GenericArg<'tcx>>,
) -> Ty<'tcx> {
    match ty.kind() {
        TyKind::Adt(def, substs) => {
            tcx.mk_adt(*def, specialize_substs(tcx, substs, generic_args_map))
        }
        TyKind::Array(elem_ty, len) => {
            //let specialized_elem_ty = specialize_type_generic_arg(tcx, elem_ty, generic_args_map);
            //let specialized_len = specialize_const_generic_arg(len, generic_args_map);
            let specialized_elem_ty = specialize_type_generic_arg(tcx, *elem_ty, generic_args_map);
            let specialized_len = specialize_const_generic_arg(*len, generic_args_map); // ???
            tcx.mk_ty(TyKind::Array(specialized_elem_ty, specialized_len))
        }
        TyKind::Param(ParamTy { name, .. }) => {
            if let Some(generic_arg) = generic_args_map.get(name) {
                return generic_arg.expect_ty();
            }
            ty
        }
        TyKind::Ref(region, ty, mutable) => {
            // let specialized_ty = specialize_type_generic_arg(tcx, ty, generic_args_map);
            let specialized_ty = specialize_type_generic_arg(tcx, *ty, generic_args_map);
            tcx.mk_ref(
                *region,
                rustc_middle::ty::TypeAndMut {
                    ty: specialized_ty,
                    mutbl: *mutable,
                },
            )
        }
        TyKind::Slice(elem_ty) => {
            // let specialized_elem_ty = specialize_type_generic_arg(tcx, elem_ty, generic_args_map);
            let specialized_elem_ty = specialize_type_generic_arg(tcx, *elem_ty, generic_args_map);
            tcx.mk_slice(specialized_elem_ty)
        }
        TyKind::RawPtr(TypeAndMut { ty, mutbl }) => {
            // let specialized_ty = specialize_type_generic_arg(tcx, ty, generic_args_map);
            let specialized_ty = specialize_type_generic_arg(tcx, *ty, generic_args_map);
            tcx.mk_ptr(rustc_middle::ty::TypeAndMut {
                ty: specialized_ty,
                mutbl: *mutbl,
            })
        }
        
        TyKind::FnDef(def_id, substs) => {
            tcx.mk_fn_def(*def_id, specialize_substs(tcx, substs, generic_args_map))
        }
        // TODO: N1 List Type    modify 20230815
        TyKind::Tuple(substs) => {
            tcx.mk_tup(// substs: List<Ty>,
                specialize_substs(
                    tcx, 
                     &(substs
                                .iter()
                                .map(|t|t.into()).collect::<Vec<GenericArg<'tcx>>>()
                            ),
                    generic_args_map
                )
                    .iter()
                    .map(|generic_arg| generic_arg.expect_ty()),
                // specialize_list(tcx, substs) // modify 
                // substs.iter(),
            )
        },
       
        
        TyKind::Closure(def_id, substs) => {
            tcx.mk_closure(*def_id, specialize_substs(tcx, substs, generic_args_map))
        }
        TyKind::FnPtr(fn_sig) => {
            let map_fn_sig = |fn_sig: FnSig<'tcx>| {
                let specialized_inputs_and_output = tcx.mk_type_list(
                    fn_sig
                        .inputs_and_output
                        .iter()
                        .map(|ty| specialize_type_generic_arg(tcx, ty, generic_args_map)),
                );
                FnSig {
                    inputs_and_output: specialized_inputs_and_output,
                    c_variadic: fn_sig.c_variadic,
                    unsafety: fn_sig.unsafety,
                    abi: fn_sig.abi,
                }
            };
            let specialized_fn_sig = fn_sig.map_bound(map_fn_sig);
            tcx.mk_fn_ptr(specialized_fn_sig)
        }
        
        TyKind::Alias(AliasKind::Projection, projection) => {
            let specialized_substs = specialize_substs(tcx, projection.substs, generic_args_map);
            let item_def_id = projection.def_id; // modify 13-2 cannot mofify

            if are_concrete(specialized_substs) {
                let param_env = tcx.param_env(tcx.associated_item(item_def_id).container_id(tcx)); // modify 13-3 cannot mofify  //tap1
                if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
                    tcx,
                    param_env,
                    item_def_id,
                    specialized_substs,
                ) {
                    let item_def_id = instance.def.def_id();
                    let item_type = tcx.type_of(item_def_id);
                    let map = generate_generic_args_map(tcx, item_def_id, instance.substs);
                    if item_type == ty && map.is_empty() {
                        // Can happen if the projection just adds a life time
                        item_type
                    } else {
                        specialize_type_generic_arg(tcx, item_type, &map)
                    }
                } else {
                    if specialized_substs.len() == 1
                        && tcx.parent(item_def_id) == tcx.lang_items().discriminant_kind_trait().unwrap()
                    // modify 13-4 cannot mofify
                    {
                        let enum_arg = specialized_substs[0];
                        if let GenericArgKind::Type(enum_ty) = enum_arg.unpack() {
                            return enum_ty.discriminant_ty(tcx);
                        }
                    }
                    debug!("could not resolve an associated type with concrete type arguments");
                    ty
                }
            } else {
                tcx.mk_projection(projection.def_id, specialized_substs) // modify 13-5 cannot mofify
            }
        }
        TyKind::Dynamic(predicates, region, dykind) => {
            let specialized_predicates = tcx.mk_poly_existential_predicates(predicates.iter().map(
                |pred: rustc_middle::ty::Binder<ExistentialPredicate<'tcx>>| {
                    //rustc_middle::ty::Binder::bind(  //???
                    
                    rustc_middle::ty::Binder::dummy(
                        // modify 15
                        match pred.skip_binder() {
                            ExistentialPredicate::Trait(ExistentialTraitRef { def_id, substs }) => {
                                ExistentialPredicate::Trait(ExistentialTraitRef {
                                    def_id,
                                    substs: specialize_substs(tcx, substs, generic_args_map),
                                })
                            }
                            ExistentialPredicate::Projection(ExistentialProjection {
                                // modify 16
                                //item_def_id,
                                def_id,
                                substs,
                                //ty,
                                term
                            }) =>{
                                if let Some(term_ty) = term.ty(){
                                    ExistentialPredicate::Projection(ExistentialProjection {
                                        //item_def_id,
                                        def_id,
                                        substs: specialize_substs(tcx, substs, generic_args_map),
                                        //ty: specialize_type_generic_arg(tcx, ty, generic_args_map),
                                        term: specialize_type_generic_arg(tcx, term_ty, generic_args_map).into(),
                                    })
                                }else{
                                    ExistentialPredicate::Projection(ExistentialProjection {
                                        //item_def_id,
                                        def_id,
                                        substs: specialize_substs(tcx, substs, generic_args_map),
                                        //ty: specialize_type_generic_arg(tcx, ty, generic_args_map),
                                        term: specialize_type_generic_arg(tcx, ty, generic_args_map).into(),
                                    })
                                }

                            } , //
                            ExistentialPredicate::AutoTrait(_) => pred.skip_binder(),
                        },
                        //tcx,
                    )
                },
            ));
            //tcx.mk_dynamic(specialized_predicates, region)
            //tcx.mk_dynamic(specialized_predicates, *region)
            // tcx.mk_dynamic(specialized_predicates, *region,/* DynKind */)
            tcx.mk_dynamic(specialized_predicates, *region, *dykind) // modify 18  cannot modify
        }
        
        // TyKind::Opaque(def_id, substs) => {
        //     tcx.mk_opaque(*def_id, specialize_substs(tcx, substs, generic_args_map))
        // }
        TyKind::Alias(AliasKind::Opaque, opaque) => {                       // 20230713 q1
           tcx.mk_opaque(opaque.def_id, specialize_substs(tcx, opaque.substs, generic_args_map))
        }
        
        TyKind::Uint(..)
        | TyKind::Int(..)
        | TyKind::Str
        | TyKind::Char
        | TyKind::Bool
        | TyKind::Float(..)
        | TyKind::Never => ty,
        TyKind::Generator(def_id, substs, movability) => tcx.mk_generator(
            *def_id,
            specialize_substs(tcx, substs, generic_args_map),
            *movability,
        ),
        TyKind::GeneratorWitness(bound_types) => {
            let map_types = |types: &rustc_middle::ty::List<Ty<'tcx>>| {
                tcx.mk_type_list(
                    types
                        .iter()
                        .map(|ty| specialize_type_generic_arg(tcx, ty, generic_args_map)),
                )
            };
            let specialized_types = bound_types.map_bound(map_types);
            tcx.mk_generator_witness(specialized_types)
        }
        unknown => {
            debug!("unknown ty kind {:?}", unknown);
            ty
        }
    }
}

fn specialize_const_generic_arg<'tcx>(
    constant:  Const<'tcx>, // ???
    generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
) -> Const<'tcx> {
    //if let ConstKind::Param(param_const) = constant.val
    //let Const(interned) = constant;

    if let ConstKind::Param(param_const) = constant.kind()
    // modify 19  cannot modify
    {
        if let Some(generic_arg) = generic_args_map.get(&param_const.name) {
            return generic_arg.expect_const();
        }
    }
    constant
}
