use crate::{
    control_flow::{
        cfg::{CallSite, Edge, EdgeKind, ForwardCFG, Method, Node, NodeKind},
        utils,
    },
    known_names::KnownNames,
};
use either::*;
use log::*;
use rustc_hir::Constness;
use rustc_infer::{
    infer::InferCtxt,
    traits::{FulfillmentErrorCode, Obligation, ObligationCause},
};
use rustc_middle::{
    mir::{
        self,
        terminator::{Terminator, TerminatorKind},
        BasicBlockData, Body, START_BLOCK,
    },
    ty::{
        error::TypeError,
        subst::{GenericArg, GenericArgKind, InternalSubsts, Subst, SubstsRef},
        AssocKind, GenericPredicates, Instance, InstanceDef, ParamEnv, PredicateKind, ToPredicate,
        TraitPredicate, TraitRef, TyCtxt, TyKind, TypeAndMut,
    },
};
use rustc_span::def_id::DefId;
use rustc_trait_selection::{
    infer::TyCtxtInferExt,
    traits::{FulfillmentContext, TraitEngine},
};
use std::{
    collections::{HashMap, HashSet, LinkedList},
    iter::FromIterator,
};

#[derive(PartialEq, Eq, Hash, Debug)]
struct VirtualCallee<'tcx> {
    trait_id: DefId,
    trait_fn: DefId,
    substs: SubstsRef<'tcx>,
}

struct VirtualCallContext<'tcx> {
    call_sites: Vec<CallSite>,
    processed_substs: HashSet<SubstsRef<'tcx>>,
}

impl<'tcx> VirtualCallContext<'tcx> {
    pub fn new() -> Self {
        Self {
            call_sites: Default::default(),
            processed_substs: Default::default(),
        }
    }
    pub fn add_call_site(&mut self, call_site: CallSite) {
        self.call_sites.push(call_site);
    }

    pub fn get_call_sites(&self) -> impl Iterator<Item = &CallSite> {
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
            let basic_blocks = body.basic_blocks();
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
            let basic_blocks = body.basic_blocks();
            for bb in basic_blocks.indices() {
                let BasicBlockData { ref terminator, .. } = basic_blocks[bb];
                if let Some(terminator) = terminator {
                    match terminator.kind {
                        TerminatorKind::Call {
                            destination,
                            cleanup,
                            ..
                        } => {
                            let call_site = CallSite {
                                caller: method_index,
                                bb_id: bb.index(),
                            };
                            let callees = self.call_site_cache.get(&call_site);
                            debug_assert!(callees.is_some());
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
                            if let Some((_, dest)) = destination {
                                let dest_index = self.cfg.node_to_index[&Node {
                                    basic_block: Some(dest),
                                    belongs_to: method_index,
                                    kind: NodeKind::Normal,
                                }];
                                self.cfg
                                    .add_edge(curr_node_index, dest_index, call_to_return_edge)
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
                                            basic_block: Some(*successor),
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
                                        basic_block: Some(*successor),
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
                self.tcx
                    .item_name(self.cfg.get_method_by_index(src_weight.belongs_to).def_id),
                src_weight.basic_block,
                self.tcx
                    .item_name(self.cfg.get_method_by_index(tgt_weight.belongs_to).def_id),
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
                        .entry(adt_def.did)
                        .or_default()
                        .insert(substs);
                }
                _ => (),
            }
        }

        let lang_items = self.tcx.lang_items();
        let clone_trait = lang_items.clone_trait();

        for bb in body.basic_blocks().indices() {
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
                self.virtual_callees.entry(virtual_callee).or_insert({
                    let mut context = VirtualCallContext::new();
                    context.add_call_site(call_site);
                    context
                });
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
