use super::utils;
use crate::control_flow::{EdgeKind, EdgeWeight, ForwardCFG, Method, Node};
use crate::known_names::KnownNames;
use either::*;
use log::*;
use rustc_hir::Constness;
use rustc_infer::{
    infer::InferCtxt,
    traits::{FulfillmentErrorCode, Obligation, ObligationCause},
};
use rustc_middle::{
    mir::START_BLOCK,
    ty::{
        error::TypeError,
        subst::{GenericArg, GenericArgKind, InternalSubsts, Subst, SubstsRef},
        AssocKind, Const, ConstKind, ExistentialPredicate, ExistentialProjection,
        ExistentialTraitRef, FnSig, GenericPredicates, Instance, ParamTy, PredicateKind,
        ToPredicate, TraitPredicate, TraitRef, Ty, TyCtxt, TypeAndMut,
    },
};
use rustc_middle::{
    mir::{
        self,
        terminator::{Terminator, TerminatorKind},
        BasicBlockData, Body,
    },
    ty::{DefIdTree, InstanceDef, ParamEnv, TyKind},
};
use rustc_span::{def_id::DefId, Symbol};
use rustc_trait_selection::{
    infer::TyCtxtInferExt,
    traits::{FulfillmentContext, TraitEngine},
};
use std::{
    collections::{BTreeSet, HashMap, HashSet, LinkedList},
    iter::FromIterator,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct CallSite<'tcx> {
    caller: Method<'tcx>,
    bb_id: usize,
}

#[derive(PartialEq, Eq, Hash, Debug)]
struct VirtualCallee<'tcx> {
    trait_id: DefId,
    trait_fn: DefId,
    substs: SubstsRef<'tcx>,
}

struct VirtualCallContext<'tcx> {
    call_sites: Vec<CallSite<'tcx>>,
    processed_substs: HashSet<SubstsRef<'tcx>>,
}

impl<'tcx> VirtualCallContext<'tcx> {
    pub fn new() -> Self {
        Self {
            call_sites: Default::default(),
            processed_substs: Default::default(),
        }
    }
    pub fn add_call_site(&mut self, call_site: CallSite<'tcx>) {
        self.call_sites.push(call_site);
    }

    pub fn get_call_sites(&self) -> impl Iterator<Item = &CallSite<'tcx>> {
        self.call_sites.iter()
    }

    pub fn add_processed_substs(&mut self, substs: SubstsRef<'tcx>) {
        self.processed_substs.insert(substs);
    }

    pub fn is_processed_substs(&self, substs: SubstsRef<'tcx>) -> bool {
        self.processed_substs.contains(substs)
    }
}

impl<'tcx> VirtualCallee<'tcx> {
    fn probe_possible_callees(
        &self,
        tcx: TyCtxt<'tcx>,
        substs_infos: &HashMap<DefId, HashSet<SubstsRef<'tcx>>>,
        context: &mut VirtualCallContext<'tcx>,
    ) -> Vec<Method<'tcx>> {
        let mut candidates = vec![];
        for impl_id in tcx.all_impls(self.trait_id) {
            match tcx.type_of(impl_id).kind() {
                TyKind::Adt(adt_def, adt_substs) => {
                    let adt_id = adt_def.did;
                    let substs_set = substs_infos.get(&adt_id);
                    if substs_set.is_none() {
                        continue;
                    }

                    let substs_set = substs_set.unwrap();
                    for substs in substs_set {
                        if context.is_processed_substs(substs) {
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
                            context.add_processed_substs(substs);
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

                        tcx.infer_ctxt().enter(|infcx| {
                            let mut fulfill_cx = FulfillmentContext::new();
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
                            let trait_predicate = PredicateKind::Trait(
                                TraitPredicate { trait_ref },
                                // A const trait bound looks like:
                                // ```
                                // struct Foo<Bar> where Bar: const Baz { ... }
                                // ```
                                // For now we don't take this situation into consideration.
                                Constness::NotConst,
                            )
                            .to_predicate(tcx);

                            let trait_predicate = trait_predicate.subst(tcx, rebased_substs);
                            let obligation = Obligation::new(
                                ObligationCause::dummy(),
                                param_env,
                                trait_predicate,
                            );

                            fulfill_cx.register_predicate_obligation(&infcx, obligation.clone());
                            // Drives compiler to do type checking and constraint solving.
                            if let Err(err) = fulfill_cx.select_all_or_error(&infcx) {
                                debug!(
                                    "candidate selecting failed: `{:?}` doesn't implements `{:?}`, due to `{:?}`",
                                    trait_ref.substs, trait_ref.def_id, err
                                );
                            } else {
                                let predicates = tcx.predicates_of(impl_id);
                                predicates.predicates.iter().for_each(|(predicate, _)| {
                                    let kind = predicate.kind().skip_binder();
                                    match kind {
                                        PredicateKind::Trait(..) | PredicateKind::Projection(..) => (),
                                        unknown => todo!("unknown predicate kind `{:?}`", unknown),
                                    }
                                });

                                let assoc_items = tcx.associated_items(impl_id);
                                let target_name = tcx.item_name(self.trait_fn);
                                let mut assoc_fn = assoc_items.in_definition_order().filter_map(|assoc_item| {
                                    if assoc_item.kind == AssocKind::Fn && assoc_item.ident.name == target_name {
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
                                    candidates.push(Method {
                                        def_id,
                                        substs: tcx.mk_substs(instantiate_substs.iter()),
                                        self_ty: None
                                    })
                                } else {
                                    todo!("default impl");
                                }
                                context.add_processed_substs(substs);
                            }
                        });
                    }
                }
                _ => (),
            }
        }
        candidates
    }

    fn instantiate_proj_substs(
        tcx: TyCtxt<'tcx>,
        predicates: GenericPredicates<'tcx>,
        substs: SubstsRef<'tcx>,
        param_env: ParamEnv<'tcx>,
        fulfill_cx: &mut FulfillmentContext<'tcx>,
        infcx: &InferCtxt<'_, 'tcx>,
    ) -> Vec<GenericArg<'tcx>> {
        let mut instantiated_substs = Vec::from_iter(substs);
        loop {
            let predicates = predicates
                .instantiate_own(tcx, tcx.mk_substs(instantiated_substs.iter()))
                .predicates;

            let mut substituted = false;
            for predicate in predicates {
                if let PredicateKind::Projection(..) = predicate.kind().skip_binder() {
                    let obligation =
                        Obligation::new(ObligationCause::dummy(), param_env, predicate);
                    fulfill_cx.register_predicate_obligation(&infcx, obligation);
                    let select_result = fulfill_cx.select_all_or_error(&infcx);
                    if let Err(errors) = select_result {
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

pub struct CHABuilder<'graph, 'tcx> {
    cfg: &'graph mut ForwardCFG<'tcx>,
    tcx: TyCtxt<'tcx>,
    work_list: LinkedList<Method<'tcx>>,
    processed_methods: BTreeSet<Method<'tcx>>,
    substs_cache: HashMap<DefId, HashSet<SubstsRef<'tcx>>>,
    virtual_callees: HashMap<VirtualCallee<'tcx>, VirtualCallContext<'tcx>>,
    call_site_cache: HashMap<CallSite<'tcx>, HashSet<Method<'tcx>>>,
}

impl<'graph, 'tcx> CHABuilder<'graph, 'tcx> {
    pub fn new(cfg: &'graph mut ForwardCFG<'tcx>) -> Self {
        let tcx = cfg.tcx;
        Self {
            cfg,
            tcx,
            work_list: Default::default(),
            processed_methods: Default::default(),
            substs_cache: Default::default(),
            virtual_callees: Default::default(),
            call_site_cache: Default::default(),
        }
    }

    pub fn build(&mut self, entry_points: impl IntoIterator<Item = DefId>) -> Vec<Method<'tcx>> {
        let empty_substs = self.tcx.intern_substs(&[]);
        let entry_points = entry_points
            .into_iter()
            .map(|def_id| Method {
                def_id,
                substs: empty_substs,
                self_ty: None,
            })
            .collect::<Vec<_>>();
        for entry_point in &entry_points {
            self.insert_task(*entry_point, None);
        }
        let entry_points = Vec::from_iter(self.work_list.clone().into_iter());

        loop {
            if let Some(method) = self.work_list.pop_front() {
                debug!("process: {:?}", method);
                let def_id = method.def_id;
                let body = self.tcx.optimized_mir(def_id);
                self.visit_body(method, body);
                self.processed_methods.insert(method);
            } else {
                let mut no_new_callee_found = true;
                let mut new_tasks = vec![];
                for (callee, context) in self.virtual_callees.iter_mut() {
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

        debug_assert!(self.cfg.method_start_point.is_empty());
        debug_assert!(self.cfg.method_end_points.is_empty());
        debug_assert!(self.cfg.node_to_index.is_empty());
        debug_assert!(self.cfg.method_basic_blocks.is_empty());

        for method in &self.processed_methods {
            let def_id = method.def_id;
            if self.is_special_method(def_id) {
                continue;
            }

            let body = self.tcx.optimized_mir(def_id);
            let basic_blocks = body.basic_blocks();
            let mut bb_to_index = HashMap::new();
            for bb in basic_blocks.indices() {
                let basic_block_data = basic_blocks[bb].clone();
                self.cfg
                    .method_basic_blocks
                    .entry(def_id)
                    .or_default()
                    .insert(bb, basic_block_data);
                let node = Node {
                    basic_block: bb,
                    belongs_to: *method,
                };
                let index = self.cfg.add_node(node);
                self.cfg.node_to_index.insert(node, index);
                if bb == START_BLOCK {
                    self.cfg.method_start_point.insert(*method, node);
                }
                bb_to_index.insert(bb, (index, node));
            }

            let normal_edge = EdgeWeight {
                container: Some(*method),
                kind: EdgeKind::Normal,
                is_certain: true,
            };
            let call_to_return_edge = EdgeWeight {
                container: Some(*method),
                kind: EdgeKind::CallToReturn,
                is_certain: true,
            };

            for bb in basic_blocks.indices() {
                let BasicBlockData { ref terminator, .. } = basic_blocks[bb];
                if let Some(terminator) = terminator {
                    let cfg = &mut self.cfg;
                    let mut add_edge = |from, to, edge| {
                        cfg.add_edge(bb_to_index[&from].0, bb_to_index[to].0, edge)
                    };

                    match &terminator.kind {
                        TerminatorKind::Goto { target } => add_edge(bb, target, normal_edge),
                        TerminatorKind::Call {
                            destination,
                            cleanup,
                            ..
                        } => {
                            if let Some((_, dest)) = destination {
                                add_edge(bb, dest, call_to_return_edge)
                            }

                            if let Some(cleanup) = cleanup {
                                add_edge(bb, cleanup, call_to_return_edge)
                            }
                        }
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
                            let node = &bb_to_index[&bb].1;
                            self.cfg
                                .method_end_points
                                .entry(*method)
                                .or_insert(vec![])
                                .push(*node);
                        }
                        _ => (),
                    }
                }
            }
        }

        for method in &self.processed_methods {
            let def_id = method.def_id;
            if self.is_special_method(def_id) {
                debug!("special caller: {:?}", def_id);
                continue;
            }

            let body = self.tcx.optimized_mir(def_id);
            let basic_blocks = body.basic_blocks();
            if basic_blocks.is_empty() {
                debug!("the body of `{:?} is empty`", def_id);
            }
            for bb in basic_blocks.indices() {
                let BasicBlockData { ref terminator, .. } = basic_blocks[bb];
                if let Some(terminator) = terminator {
                    match terminator.kind {
                        TerminatorKind::Call { .. } => {
                            let call_site = CallSite {
                                caller: *method,
                                bb_id: bb.index(),
                            };
                            let callees = self.call_site_cache.get(&call_site);
                            debug_assert!(callees.is_some());
                            let callees = callees.unwrap();
                            debug_assert!(!callees.is_empty());
                            let is_certain = callees.len() == 1;
                            for callee in callees {
                                if self.is_special_method(callee.def_id) {
                                    debug!("special callee: {:?}", callee.def_id);
                                    continue;
                                }

                                let mut current_node = Node {
                                    basic_block: bb,
                                    belongs_to: *method,
                                };

                                let callee_start_point = self.cfg.method_start_point[callee];
                                self.cfg.add_edge(
                                    self.cfg.node_to_index[&current_node],
                                    self.cfg.node_to_index[&callee_start_point],
                                    EdgeWeight {
                                        container: None,
                                        kind: EdgeKind::Call,
                                        is_certain,
                                    },
                                );

                                let end_points = self.cfg.method_end_points[&callee].clone();
                                let successors = terminator.kind.successors();
                                for successor in successors {
                                    current_node.basic_block = *successor;
                                    for end_point in &end_points {
                                        self.cfg.add_edge(
                                            self.cfg.node_to_index[&end_point],
                                            self.cfg.node_to_index[&current_node],
                                            EdgeWeight {
                                                container: None,
                                                kind: EdgeKind::Return,
                                                is_certain: true,
                                            },
                                        )
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
        }

        entry_points
    }

    fn is_special_method(&self, def_id: DefId) -> bool {
        let known_name = KnownNames::get(self.tcx, def_id);
        KnownNames::is_known_name_for_liquid(known_name) || known_name == KnownNames::Alloc
    }

    fn visit_body(&mut self, method: Method<'tcx>, body: &'tcx Body<'tcx>) {
        let local_decls = &body.local_decls;
        for local_decl in local_decls {
            let local_ty = local_decl.ty;
            match local_ty.kind() {
                TyKind::Adt(adt_def, substs) => {
                    let map = self.generate_generic_args_map(method.def_id, method.substs);
                    let substs = self.specialize_substs(substs, &map);
                    self.substs_cache
                        .entry(adt_def.did)
                        .or_default()
                        .insert(substs);
                }
                _ => (),
            }
        }
        for bb in body.basic_blocks().indices() {
            let BasicBlockData { ref terminator, .. } = body[bb];

            if let Some(terminator) = terminator {
                let Terminator { kind, .. } = terminator;
                if let TerminatorKind::Call { func, args, .. } = kind {
                    let bb_id = bb.index();
                    let call_kind = func.ty(local_decls, self.tcx).kind();

                    match call_kind {
                        TyKind::FnDef(def_id, substs) => {
                            let callee = Method {
                                def_id: *def_id,
                                substs,
                                self_ty: None,
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
        let call_site = CallSite { caller, bb_id };
        match self.resolve(caller, callee, args) {
            Left(callee) => {
                self.insert_task(callee, Some(call_site));
            }
            Right(virtual_callee) => {
                self.virtual_callees.entry(virtual_callee).or_insert({
                    let mut context = VirtualCallContext::new();
                    context.add_call_site(call_site);
                    context
                });
            }
        }
    }

    fn insert_task(&mut self, mut callee: Method<'tcx>, call_site: Option<CallSite<'tcx>>) {
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
                    callee.self_ty = Some(self.tcx.mk_adt(adt_def, substs));
                }
                TyKind::Param(param_ty) => {
                    let index = param_ty.index;
                    callee.self_ty = Some(callee.substs[index as usize].expect_ty());
                }
                TyKind::Ref(region, ty, mutbl) => {
                    if let TyKind::Param(param_ty) = ty.kind() {
                        let index = param_ty.index;
                        callee.self_ty = Some(self.tcx.mk_ref(
                            region,
                            TypeAndMut {
                                ty: callee.substs[index as usize].expect_ty(),
                                mutbl: *mutbl,
                            },
                        ));
                    } else {
                        if utils::is_concrete(ty.kind()) {
                            callee.self_ty = Some(impl_ty);
                        } else {
                            todo!(
                                "encounter unknown self type `{:?}` for `{:?}`",
                                impl_kind,
                                callee.def_id,
                            );
                        }
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

        if callee.def_id.is_local() {
            if !self.processed_methods.contains(&callee) {
                self.work_list.push_back(callee);
            }
        } else {
            let callee_id = callee.def_id;
            if self.tcx.is_mir_available(callee_id) {
                if self.is_special_method(callee_id) {
                    self.processed_methods.insert(callee);
                }
                if !self.processed_methods.contains(&callee) {
                    self.work_list.push_back(callee);
                }
            } else {
                debug!("the mir of `{:?}` is not available", callee_id);
                self.processed_methods.insert(callee);
            }
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
                    let map = self.generate_generic_args_map(caller.def_id, caller.substs);
                    let callee_substs = self.specialize_substs(callee.substs, &map);
                    let ty = callee_substs[0].expect_ty();
                    match ty.kind() {
                        TyKind::Closure(callee_id, callee_substs)
                        | TyKind::FnDef(callee_id, callee_substs) => {
                            let actual_callee = Method {
                                def_id: *callee_id,
                                substs: callee_substs,
                                self_ty: None,
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
        let map = self.generate_generic_args_map(caller.def_id, caller.substs);
        let callee_substs = self.specialize_substs(callee.substs, &map);
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
                    let substs = self.specialize_substs(instance.substs, &map);
                    return Left(Method {
                        def_id: instance.def_id(),
                        substs,
                        self_ty: None,
                    });
                }
            }
        } else {
            todo!(
                "unable to resolve callee {{ def_id: {:?}, substs: {:?} }}",
                callee.def_id,
                callee.substs,
            );
        }
    }

    fn generate_generic_args_map(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> HashMap<Symbol, GenericArg<'tcx>> {
        let mut map = HashMap::new();
        InternalSubsts::for_item(self.tcx, def_id, |param_def, _| {
            if let Some(generic_arg) = substs.get(param_def.index as usize) {
                map.insert(param_def.name, *generic_arg);
            } else {
                todo!("unmapped generic param definition: {:?}", param_def);
            }
            self.tcx.mk_param_from_def(param_def)
        });
        map
    }

    fn specialize_substs(
        &self,
        substs: &[GenericArg<'tcx>],
        generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
    ) -> SubstsRef<'tcx> {
        let specialized_generic_args = substs
            .iter()
            .map(|generic_arg| self.specialize_generic_arg(&generic_arg, generic_args_map))
            .collect::<Vec<_>>();
        self.tcx.intern_substs(&specialized_generic_args)
    }

    fn specialize_generic_arg(
        &self,
        generic_arg: &GenericArg<'tcx>,
        generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
    ) -> GenericArg<'tcx> {
        match generic_arg.unpack() {
            GenericArgKind::Type(ty) => self
                .specialize_type_generic_arg(ty, generic_args_map)
                .into(),
            GenericArgKind::Const(constant) => self
                .specialize_const_generic_arg(constant, generic_args_map)
                .into(),
            _ => *generic_arg,
        }
    }

    fn specialize_type_generic_arg(
        &self,
        ty: Ty<'tcx>,
        generic_args_map: &HashMap<rustc_span::Symbol, GenericArg<'tcx>>,
    ) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Adt(def, substs) => self
                .tcx
                .mk_adt(def, self.specialize_substs(substs, generic_args_map)),
            TyKind::Array(elem_ty, len) => {
                let specialized_elem_ty =
                    self.specialize_type_generic_arg(elem_ty, generic_args_map);
                let specialized_len = self.specialize_const_generic_arg(len, generic_args_map);
                self.tcx
                    .mk_ty(TyKind::Array(specialized_elem_ty, specialized_len))
            }
            TyKind::Param(ParamTy { name, .. }) => {
                if let Some(generic_arg) = generic_args_map.get(name) {
                    return generic_arg.expect_ty();
                }
                ty
            }
            TyKind::Ref(region, ty, mutable) => {
                let specialized_ty = self.specialize_type_generic_arg(ty, generic_args_map);
                self.tcx.mk_ref(
                    region,
                    rustc_middle::ty::TypeAndMut {
                        ty: specialized_ty,
                        mutbl: *mutable,
                    },
                )
            }
            TyKind::Slice(elem_ty) => {
                let specialized_elem_ty =
                    self.specialize_type_generic_arg(elem_ty, generic_args_map);
                self.tcx.mk_slice(specialized_elem_ty)
            }
            TyKind::RawPtr(TypeAndMut { ty, mutbl }) => {
                let specialized_ty = self.specialize_type_generic_arg(ty, generic_args_map);
                self.tcx.mk_ptr(rustc_middle::ty::TypeAndMut {
                    ty: specialized_ty,
                    mutbl: *mutbl,
                })
            }
            TyKind::FnDef(def_id, substs) => self
                .tcx
                .mk_fn_def(*def_id, self.specialize_substs(substs, generic_args_map)),
            TyKind::Tuple(substs) => self.tcx.mk_tup(
                self.specialize_substs(substs, generic_args_map)
                    .iter()
                    .map(|generic_arg| generic_arg.expect_ty()),
            ),
            TyKind::Closure(def_id, substs) => self
                .tcx
                .mk_closure(*def_id, self.specialize_substs(substs, generic_args_map)),
            TyKind::FnPtr(fn_sig) => {
                let map_fn_sig = |fn_sig: FnSig<'tcx>| {
                    let specialized_inputs_and_output = self.tcx.mk_type_list(
                        fn_sig
                            .inputs_and_output
                            .iter()
                            .map(|ty| self.specialize_type_generic_arg(ty, generic_args_map)),
                    );
                    FnSig {
                        inputs_and_output: specialized_inputs_and_output,
                        c_variadic: fn_sig.c_variadic,
                        unsafety: fn_sig.unsafety,
                        abi: fn_sig.abi,
                    }
                };
                let specialized_fn_sig = fn_sig.map_bound(map_fn_sig);
                self.tcx.mk_fn_ptr(specialized_fn_sig)
            }
            TyKind::Projection(projection) => {
                let specialized_substs =
                    self.specialize_substs(projection.substs, generic_args_map);
                let item_def_id = projection.item_def_id;

                if utils::are_concrete(specialized_substs) {
                    let param_env = self
                        .tcx
                        .param_env(self.tcx.associated_item(item_def_id).container.id());
                    if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
                        self.tcx,
                        param_env,
                        item_def_id,
                        specialized_substs,
                    ) {
                        let item_def_id = instance.def.def_id();
                        let item_type = self.tcx.type_of(item_def_id);
                        let map = self.generate_generic_args_map(item_def_id, instance.substs);
                        if item_type == ty && map.is_empty() {
                            // Can happen if the projection just adds a life time
                            item_type
                        } else {
                            self.specialize_type_generic_arg(item_type, &map)
                        }
                    } else {
                        if specialized_substs.len() == 1
                            && self.tcx.parent(item_def_id)
                                == self.tcx.lang_items().discriminant_kind_trait()
                        {
                            let enum_arg = specialized_substs[0];
                            if let GenericArgKind::Type(enum_ty) = enum_arg.unpack() {
                                return enum_ty.discriminant_ty(self.tcx);
                            }
                        }
                        debug!("could not resolve an associated type with concrete type arguments");
                        ty
                    }
                } else {
                    self.tcx
                        .mk_projection(projection.item_def_id, specialized_substs)
                }
            }
            TyKind::Dynamic(predicates, region) => {
                let specialized_predicates =
                    self.tcx
                        .mk_poly_existential_predicates(predicates.iter().map(
                            |pred: rustc_middle::ty::Binder<ExistentialPredicate<'tcx>>| {
                                rustc_middle::ty::Binder::bind(
                                    match pred.skip_binder() {
                                        ExistentialPredicate::Trait(ExistentialTraitRef {
                                            def_id,
                                            substs,
                                        }) => ExistentialPredicate::Trait(ExistentialTraitRef {
                                            def_id,
                                            substs: self
                                                .specialize_substs(substs, generic_args_map),
                                        }),
                                        ExistentialPredicate::Projection(
                                            ExistentialProjection {
                                                item_def_id,
                                                substs,
                                                ty,
                                            },
                                        ) => ExistentialPredicate::Projection(
                                            ExistentialProjection {
                                                item_def_id,
                                                substs: self
                                                    .specialize_substs(substs, generic_args_map),
                                                ty: self.specialize_type_generic_arg(
                                                    ty,
                                                    generic_args_map,
                                                ),
                                            },
                                        ),
                                        ExistentialPredicate::AutoTrait(_) => pred.skip_binder(),
                                    },
                                    self.tcx,
                                )
                            },
                        ));
                self.tcx.mk_dynamic(specialized_predicates, region)
            }
            unknown => {
                if !matches!(
                    unknown,
                    TyKind::Uint(..) | TyKind::Int(..) | TyKind::Str | TyKind::Char
                ) {
                    debug!("unknown ty kind {:?}", unknown);
                }
                ty
            }
        }
    }

    fn specialize_const_generic_arg(
        &self,
        constant: &'tcx Const<'tcx>,
        generic_args_map: &HashMap<Symbol, GenericArg<'tcx>>,
    ) -> &'tcx Const<'tcx> {
        if let ConstKind::Param(param_const) = constant.val {
            if let Some(generic_arg) = generic_args_map.get(&param_const.name) {
                return generic_arg.expect_const();
            }
        }
        constant
    }
}
