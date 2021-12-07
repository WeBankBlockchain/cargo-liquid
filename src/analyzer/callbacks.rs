// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;

use crate::{
    control_flow::{
        utils, BackwardCFG, Builder, EdgeKind, ForwardCFG, InterproceduralCFG, Method, MethodIndex,
    },
    ifds::{problems::*, IfdsSolver},
    known_names::KnownNames,
};
use either::*;
use itertools::Itertools;
use log::*;
use petgraph::visit::Dfs;
use rustc_driver::Compilation;
use rustc_hir::{def::DefKind, def_id::DefId, definitions::DefPathData};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{
    mir::{
        BindingForm, Body, ClearCrossCrate, ImplicitSelfKind, Local, LocalInfo, Operand,
        TerminatorKind,
    },
    ty::{DefIdTree, Ty, TyCtxt, TyKind, Visibility},
};
use serde::Serialize;
use std::{
    collections::{HashMap, HashSet, LinkedList},
    env, fs,
    ops::Deref,
    path::PathBuf,
};

#[derive(Debug)]
pub struct MethodAttr {
    pub mutable: bool,
    pub visible: bool,
    pub name: String,
}

pub struct AnalysisCallbacks {
    pub cfg_path: Option<PathBuf>,
}

const STORAGE_NS: [&str; 3] = ["Storage", "__liquid_storage", "__liquid_private"];
const INTERFACE_NS: [&str; 3] = ["Interface", "__liquid_interface", "__liquid_private"];

impl rustc_driver::Callbacks for AnalysisCallbacks {
    /// Called after the compiler has completed all analysis passes and before it
    /// lowers MIR to LLVM IR. At this point the compiler is ready to tell us all
    /// it knows and we can proceed to do analysis of all of the functions that
    /// will end up in the compiler output.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| self.analyze_with_mir(compiler, tcx));

        // This is only a analyzer, cargo still needs code generation to work.
        Compilation::Continue
    }
}

mod field_kind {
    pub type Type = u8;

    /// `0` represents `All`, which means the contract attempts to visit a `Value<T>` or the
    /// key for reading/writing other types of containers can not be inferred during static
    /// program analysis.
    pub const ALL: Type = 0;
    /// `1` represents `Len`, which means the contract may change length of some a container.
    /// It's only meaningful to containers such like `Vec<T>`, `Mapping<K, V>` or
    /// `IterableMapping<K, V>`.
    pub const LEN: Type = 1;
    /// `2` represents `Env`, which means the contract wants to use some values from
    /// execution context as keys to visit containers.
    pub const ENV: Type = 2;
    /// `3` represents `Var`, which means the contract wants to use some values from method
    /// parameters as keys to visit containers.
    pub const VAR: Type = 3;
    /// `4` represents `Const`, which means the contract wants to use some constant values as
    /// keys to visit containers.
    pub const CONST: Type = 4;
}

mod env_info_kind {
    pub type Type = usize;

    /// `0` represents caller of transaction.
    pub const CALLER: Type = 0;
    /// `1` represents origin sender of transaction.
    pub const ORIGIN: Type = 1;
    /// `2` represents timestamp of current block.
    pub const NOW: Type = 2;
    /// `3` represents height of current block.
    pub const BLOCK_NUMBER: Type = 3;
    /// `4` represents self address of current contract.
    pub const ADDR: Type = 4;
}

impl AnalysisCallbacks {
    fn analyze_conflict_fields<'tcx>(
        &self,
        mut_methods: &Vec<MethodIndex>,
        external_methods: &HashMap<DefId, MethodAttr>,
        tcx: TyCtxt<'tcx>,
        fwd_cfg: &ForwardCFG<'tcx>,
        storage_ty: Ty<'tcx>,
    ) {
        #[derive(Serialize, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Debug)]
        struct FieldDesc {
            /// The index of which state variable will be visited.
            slot: usize,
            kind: field_kind::Type,
            /// If `kind` equals to `All` or `Len`, then `path` must be empty;
            ///
            /// if `kind` equals to `Env`, then `path` must only contain one element, and the element
            /// represents which kind of context information the contract needs to acquire.
            ///
            /// if `kind` equals to `Var`, then `path` contains an access path described via integer
            /// indices, e.g., "[2, 0]" means key coming from the **1st** data member of the **3rd**
            /// parameter;
            ///
            /// if `kind` equals to `Const`, the `path` contains the **raw** bytes representation of
            /// the corresponding constant value.
            path: Vec<usize>,
            /// Whether this conflict field is used to visit some a state variable mutably.
            read_only: bool,
        }

        let contains_interface_invocation = |method| {
            let mut visited = HashSet::new();
            let mut work_list = LinkedList::new();
            work_list.push_back(method);

            while !work_list.is_empty() {
                let curr_method = work_list.pop_front().unwrap();
                let call_sites = fwd_cfg.get_call_sites_within(curr_method);
                let callees = call_sites
                    .iter()
                    .map(|call_site| fwd_cfg.get_callees_of_call_at(call_site))
                    .flatten()
                    .collect::<Vec<_>>();

                for callee in callees {
                    let callee_id = callee.def_id;
                    if external_methods.contains_key(&callee_id) {
                        return true;
                    }

                    if !visited.contains(callee) {
                        visited.insert(callee);
                        work_list.push_back(callee);
                    }
                }
            }
            false
        };

        let target_dir = PathBuf::from(env::var("LIQUID_ANALYSIS_TARGET_DIR").unwrap());
        let bwd_cfg = BackwardCFG::new(&fwd_cfg);
        let mut field_descs = HashMap::new();

        for method_index in mut_methods {
            let method_index = *method_index;
            let method = bwd_cfg.get_method_by_index(method_index);
            let results = if contains_interface_invocation(method) {
                HashSet::new()
            } else {
                let problem = ConflictFields::new(tcx, &bwd_cfg, method_index, storage_ty);
                let mut ifds_solver = IfdsSolver::new(problem, &bwd_cfg, true);
                ifds_solver.solve();
                let end_point = bwd_cfg.get_end_points_of(method);
                debug_assert!(end_point.len() == 1);
                let end_point = end_point[0];
                ifds_solver.get_results_at(end_point)
            };

            let method_id = method.def_id;
            let fn_name = tcx.item_name(method_id);
            let fn_name = format!("{}", fn_name.as_str());
            let mut conflict_fields = results
                .iter()
                .map(|conflict_field| {
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = conflict_field
                    {
                        let (kind, path) = match key {
                            Key::All => (field_kind::ALL, vec![]),
                            Key::Len => (field_kind::LEN, vec![]),
                            Key::Env(env_kind) => (
                                field_kind::ENV,
                                vec![match env_kind {
                                    EnvKind::Caller => env_info_kind::CALLER,
                                    EnvKind::Origin => env_info_kind::ORIGIN,
                                    EnvKind::Now => env_info_kind::NOW,
                                    EnvKind::BlockNumber => env_info_kind::BLOCK_NUMBER,
                                    EnvKind::Address => env_info_kind::ADDR,
                                }],
                            ),
                            Key::Var(def_id, access_path) => {
                                if def_id != &method_id {
                                    (field_kind::ALL, vec![])
                                } else {
                                    let body = tcx.optimized_mir(method_id);
                                    let arg_count = body.arg_count;
                                    let base = access_path.base;
                                    if base.index() > arg_count {
                                        (field_kind::ALL, vec![])
                                    } else {
                                        let mut path = vec![base.index() - 2];
                                        path.extend(access_path.fields.iter());
                                        (field_kind::VAR, path)
                                    }
                                }
                            }
                            Key::Const(bytes) => (
                                field_kind::CONST,
                                bytes.iter().map(|byte| *byte as usize).collect::<Vec<_>>(),
                            ),
                        };

                        FieldDesc {
                            slot: *container,
                            kind,
                            path,
                            read_only: *read_only,
                        }
                    } else {
                        unreachable!()
                    }
                })
                .collect::<Vec<_>>();

            conflict_fields.sort();
            conflict_fields.dedup();
            let mut composed_conflict_fields: Vec<FieldDesc> = vec![];
            let mut add_to_composed = |field_to_add: FieldDesc| {
                if field_to_add.kind == field_kind::LEN {
                    composed_conflict_fields.push(field_to_add);
                    return;
                }

                if composed_conflict_fields
                    .iter()
                    .rposition(|field| {
                        field.slot == field_to_add.slot
                            && field.kind == field_kind::ALL
                            && field.read_only == field_to_add.read_only
                    })
                    .is_none()
                {
                    composed_conflict_fields.push(field_to_add);
                }
            };
            let mut i = 0;
            loop {
                if i >= conflict_fields.len() {
                    break;
                }

                if i == conflict_fields.len() - 1 {
                    add_to_composed(conflict_fields[i].clone());
                    break;
                }

                let j = i + 1;
                let field_i = &conflict_fields[i];
                let field_j = &conflict_fields[j];
                if field_i.kind == field_j.kind
                    && field_i.path == field_j.path
                    && field_i.slot == field_j.slot
                    && !field_i.read_only
                    && field_j.read_only
                {
                    add_to_composed(FieldDesc {
                        kind: field_i.kind,
                        path: field_i.path.clone(),
                        slot: field_i.slot,
                        read_only: false,
                    });
                    i = j + 1;
                } else {
                    add_to_composed(field_i.clone());
                    i += 1;
                }
            }
            if !composed_conflict_fields.is_empty() {
                field_descs.insert(fn_name, composed_conflict_fields);
            }
        }

        fs::write(
            target_dir.join("conflict_fields.analysis"),
            format!("{}", serde_json::to_string(&field_descs).unwrap()),
        )
        .unwrap();
    }

    fn analyze_uninitialized_states<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        constructor: MethodIndex,
        fwd_cfg: &ForwardCFG<'tcx>,
        storage_ty: Ty<'tcx>,
        compiler: &Compiler,
    ) {
        let problem = UninitializedStates::new(tcx, &fwd_cfg, constructor, storage_ty);
        let mut ifds_solver = IfdsSolver::new(problem, &fwd_cfg, true);
        ifds_solver.solve();

        let subgraph = fwd_cfg.graph.filter_map(
            |node_idx, _| Some(fwd_cfg.graph.node_weight(node_idx).unwrap()),
            |edge_idx, _| {
                let edge_weight = fwd_cfg.graph.edge_weight(edge_idx).unwrap();
                if edge_weight.kind == EdgeKind::Return {
                    None
                } else {
                    // Removes all `Return` edges, because theses edges can introduce unexpected child nodes when
                    // doing DFS traversing for detecting in constructor. For example:
                    //
                    // new       method_never_called_by_new
                    //  |  Call       Call  |
                    //  |----->callee<------|
                    //  |         |         |
                    //  |  Return | Return  |
                    //  |<--------|-------->|
                    //
                    // In such a situation, when traversing from start point of `new`, the nodes in `method_never_called_by_new`
                    // can be visited via the `Return` edge from `callee` to `method_never_called_by_new`, but actually this
                    // execution path is illegal, so the analysis will be trapped.
                    //
                    // After removing all `Return` edges, the legal child nodes can also be visited via `Call` edges and
                    // `CallToReturn` edges, hence the removing process has no impact on correctness of uninitialized
                    // state variables detecting.
                    Some(edge_weight)
                }
            },
        );

        let constructor = fwd_cfg.get_method_by_index(constructor);
        let start_points = fwd_cfg.get_start_points_of(constructor);
        assert!(start_points.len() == 1);

        // The `subgraph` has the structure of a subgraph of the original graph after removing all `Return` edges.
        // Petgraph guarantees that no nodes are removed, the resulting graph has compatible node indices.
        //
        // ## NOTICE
        // The above invariant is kept in petgraph of version 0.6. If upgrade version of petgraph in future, please
        // check this invariant again.
        let mut dfs = Dfs::new(&subgraph, fwd_cfg.node_to_index[start_points[0]]);
        let session = compiler.session();

        while let Some(node_index) = dfs.next(&subgraph) {
            let node = fwd_cfg.graph.node_weight(node_index).unwrap();
            if fwd_cfg.is_call(node) {
                let belongs_to = node.belongs_to;
                let method = fwd_cfg.get_method_by_index(belongs_to);
                let body = tcx.optimized_mir(method.def_id);
                let bbd = &body.basic_blocks()[node.basic_block.unwrap()];
                let terminator = bbd.terminator();
                let local_decls = &body.local_decls;

                if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                    if let TyKind::FnDef(def_id, ..) = func.ty(local_decls, tcx).kind() {
                        let fn_name = KnownNames::get(tcx, *def_id);
                        if matches!(
                            fn_name,
                            KnownNames::LiquidStorageCollectionsMappingLen
                                | KnownNames::LiquidStorageCollectionsMappingInsert
                                | KnownNames::LiquidStorageCollectionsMappingContainsKey
                                | KnownNames::LiquidStorageCollectionsMappingIndex
                                | KnownNames::LiquidStorageCollectionsMappingIndexMut
                                | KnownNames::LiquidStorageCollectionsMappingGet
                                | KnownNames::LiquidStorageCollectionsMappingGetMut
                                | KnownNames::LiquidStorageCollectionsMappingMutateWith
                                | KnownNames::LiquidStorageCollectionsMappingExtend
                                | KnownNames::LiquidStorageCollectionsMappingRemove
                                | KnownNames::LiquidStorageCollectionsMappingIsEmpty
                                | KnownNames::LiquidStorageValueGet
                                | KnownNames::LiquidStorageValueGetMut
                                | KnownNames::LiquidStorageValueMutateWith
                                | KnownNames::LiquidStorageValueSet
                                | KnownNames::LiquidStorageCollectionsVecUse
                                | KnownNames::LiquidStorageCollectionsVecIterNext
                                | KnownNames::LiquidStorageCollectionsIterableMappingUse
                                | KnownNames::LiquidStorageCollectionsIterableMappingIterNext
                        ) {
                            let results = ifds_solver.get_results_at(node);
                            let indices = results
                                .into_iter()
                                .map(|result| {
                                    if let UninitializedState::Field(index) = result {
                                        index
                                    } else {
                                        unreachable!()
                                    }
                                })
                                .collect::<HashSet<_>>();
                            if let Some(pts) = ifds_solver
                                .problem
                                .pfg
                                .get_points_to(method.def_id, args[0].place().unwrap())
                            {
                                for point_to in pts.iter() {
                                    if let Either::Right(state) = point_to {
                                        if indices.contains(&state.0) {
                                            session.span_warn(
                                                terminator.source_info.span,
                                                "state variable may be used before it is initialized",
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        let states = if let TyKind::Adt(adt_def, ..) = storage_ty.kind() {
            adt_def
                .all_fields()
                .map(|field_def| format!("`{}`", field_def.ident.name))
                .enumerate()
                .collect::<HashMap<_, _>>()
        } else {
            unreachable!("`Storage` should be a struct type")
        };
        let end_points = fwd_cfg.get_end_points_of(constructor);
        for end_point in end_points {
            let final_results = ifds_solver.get_results_at(end_point);
            if !final_results.is_empty() {
                let mut final_result = final_results
                    .into_iter()
                    .map(|result| {
                        if let UninitializedState::Field(index) = result {
                            index
                        } else {
                            unreachable!()
                        }
                    })
                    .collect::<Vec<_>>();
                final_result.sort();

                let belongs_to = end_point.belongs_to;
                let method = fwd_cfg.get_method_by_index(belongs_to);
                let body = tcx.optimized_mir(method.def_id);
                let preds = fwd_cfg.get_preds_of(end_point);
                assert!(preds.len() == 1);

                let bbd = &body.basic_blocks()[preds[0].basic_block.unwrap()];
                let terminator = bbd.terminator();
                session.span_warn(
                    terminator.source_info.span,
                    &format!(
                        "when execution of constructor exits from here,\n         \
                        these state variables may be uninitialized: {}",
                        final_result
                            .into_iter()
                            .map(|index| &states[&index])
                            .join(", ")
                    ),
                );
            }
        }
    }

    fn related_to<'tcx>(tcx: TyCtxt<'tcx>, ty: &Ty<'tcx>, tys: &HashSet<Ty<'tcx>>) -> bool {
        const VEC_ITER_NS: [&str; 6] = [
            "lang_core",
            "storage",
            "collections",
            "vec",
            "impls",
            "Iter",
        ];
        const ITERABLE_MAPPING_ITER_NS: [&str; 6] = [
            "lang_core",
            "storage",
            "collections",
            "iterable_mapping",
            "impls",
            "Iter",
        ];

        if tys.contains(ty) {
            return true;
        }

        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                let def_path = tcx
                    .def_path(adt_def.did)
                    .data
                    .iter()
                    .filter_map(|disambiguated_def_path_data| {
                        if let DefPathData::TypeNs(symbol) = disambiguated_def_path_data.data {
                            Some(symbol.as_str())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                if def_path == VEC_ITER_NS || def_path == ITERABLE_MAPPING_ITER_NS {
                    return false;
                }

                let field_tys = adt_def
                    .all_fields()
                    .map(|field_def| field_def.ty(tcx, substs))
                    .collect::<HashSet<_>>();

                field_tys
                    .iter()
                    .map(|ty| *ty)
                    .chain(substs.types())
                    .any(|ty| Self::related_to(tcx, &ty, tys))
            }
            TyKind::Slice(ty) => Self::related_to(tcx, ty, tys),
            TyKind::RawPtr(type_and_mut) => Self::related_to(tcx, &type_and_mut.ty, tys),
            TyKind::Ref(_, ty, _) => Self::related_to(tcx, ty, tys),
            TyKind::Array(ty, _) => Self::related_to(tcx, ty, tys),
            TyKind::Tuple(substs) => substs.types().any(|ty| Self::related_to(tcx, &ty, tys)),
            _ => false,
        }
    }

    fn deref_ty<'tcx>(ty: Ty<'tcx>) -> Ty {
        let mut nested_ty = ty;
        while let TyKind::Ref(_, sub_ty, _) = nested_ty.kind() {
            nested_ty = sub_ty;
        }
        nested_ty
    }

    fn type_check<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        fwd_cfg: &ForwardCFG<'tcx>,
        storage_ty: Ty<'tcx>,
        compiler: &Compiler,
    ) {
        if let TyKind::Adt(adt_def, substs) = storage_ty.kind() {
            let session = compiler.session();
            debug_assert!(adt_def.is_struct());
            let mut state_tys = adt_def
                .all_fields()
                .map(|field_def| field_def.ty(tcx, substs))
                .collect::<HashSet<_>>();
            state_tys.insert(storage_ty);

            for method in &fwd_cfg.methods {
                let def_id = method.def_id;
                if utils::is_special_method(tcx, def_id).is_some() {
                    continue;
                }

                let substs = &method.substs;
                let body = tcx.optimized_mir(def_id);
                let local_decls = &body.local_decls;
                let basic_blocks = body.basic_blocks();
                let mut indirect_call_args = HashSet::new();
                for call_site in fwd_cfg.get_call_sites_within(method) {
                    let bdd = &basic_blocks[call_site.basic_block.unwrap()];
                    let terminator = bdd.terminator();
                    if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                        let func_ty = func.ty(local_decls, tcx);
                        if let TyKind::FnDef(def_id, ..) = func_ty.kind() {
                            if matches!(
                                KnownNames::get(tcx, *def_id),
                                KnownNames::CoreOpsFunctionFnCall
                                    | KnownNames::CoreOpsFunctionFnCallMut
                                    | KnownNames::CoreOpsFunctionFnOnceCallOnce
                            ) {
                                let arg_local = match args[1] {
                                    Operand::Copy(place) | Operand::Move(place) => place.local,
                                    _ => unreachable!(),
                                };
                                indirect_call_args.insert(arg_local);
                            }
                        }
                    }
                }

                for local in local_decls.indices() {
                    if indirect_call_args.contains(&local) {
                        continue;
                    }
                    let local_decl = &local_decls[local];
                    let local_ty = local_decl.ty;
                    let concrete_local_ty = if utils::is_concrete(local_ty.kind()) {
                        local_ty
                    } else {
                        let generic_args_map =
                            utils::generate_generic_args_map(tcx, def_id, substs);
                        utils::specialize_type_generic_arg(tcx, local_ty, &generic_args_map)
                    };
                    let deref_ty = Self::deref_ty(concrete_local_ty);

                    macro_rules! report_err {
                        () => {
                            session.span_err(
                                local_decl.source_info.span,
                                &format!(
                                    "can't use container type or storage here, whose type is `{}`.\n{}",
                                    local_ty,
                                    "Note: this is an error from static analysis, if you don't need analysis results \
                                    please use `--skip-analysis` option to skip the analysis process"
                                ),
                            );
                            session.abort_if_errors();
                        };
                    }

                    if Self::related_to(tcx, &deref_ty, &state_tys) {
                        if !state_tys.contains(deref_ty) {
                            report_err!();
                        }
                    }

                    if state_tys.contains(&concrete_local_ty) {
                        report_err!();
                    }
                }
            }
        } else {
            unreachable!("`Storage` should be a struct type")
        }
    }

    fn detect_mutable_invocations<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        fwd_cfg: &ForwardCFG<'tcx>,
        imm_methods: Vec<MethodIndex>,
        external_methods: &HashMap<DefId, MethodAttr>,
        compiler: &Compiler,
    ) {
        let session = compiler.session();
        for method_index in imm_methods {
            let mut curr_method = fwd_cfg.get_method_by_index(method_index);
            let mut visited = HashSet::new();
            let mut call_path: Vec<&Method<'tcx>> = vec![];
            loop {
                let call_sites = fwd_cfg.get_call_sites_within(curr_method);
                let callees = call_sites
                    .iter()
                    .map(|call_site| fwd_cfg.get_callees_of_call_at(call_site))
                    .flatten()
                    .collect::<Vec<_>>();

                let mut found_unvisited = false;
                for callee in callees {
                    let callee_id = callee.def_id;
                    if external_methods.contains_key(&callee_id) {
                        let attr = &external_methods[&callee_id];
                        if attr.mutable {
                            let call_path_msg = call_path
                                .iter()
                                .chain(&[curr_method])
                                .map(|method| {
                                    if let Some(ident) = tcx.opt_item_name(method.def_id) {
                                        let fn_name = String::from(ident.name.as_str().deref());
                                        if method.substs.is_empty() {
                                            fn_name
                                        } else {
                                            format!(
                                                "{}<{}>",
                                                fn_name,
                                                method
                                                    .substs
                                                    .iter()
                                                    .map(|generic| format!(
                                                        "{}",
                                                        generic.expect_ty()
                                                    ))
                                                    .join(", ")
                                            )
                                        }
                                    } else {
                                        format!("{:?}", method.def_id)
                                    }
                                })
                                .join(" -> ");
                            session.span_warn(
                                tcx.def_span(callee_id),
                                &format!(
                                    "attempt to invoke this \
                                    mutable external interface from an immutable entry point,\
                                    \n         while previous call path is `{}`",
                                    &call_path_msg
                                ),
                            );
                        }
                        continue;
                    }

                    if !visited.contains(callee) {
                        call_path.push(curr_method);
                        visited.insert(callee);
                        curr_method = callee;
                        found_unvisited = true;
                        break;
                    }
                }

                if found_unvisited {
                    continue;
                }
                if let Some(node) = call_path.pop() {
                    curr_method = node;
                } else {
                    break;
                }
            }
        }
    }

    fn analyze_with_mir<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) {
        let (contract_methods, external_methods) = Self::collect_method_attrs(tcx);
        let mut fwd_cfg = ForwardCFG::new(tcx);
        let mut cfg_builder = Builder::new(&mut fwd_cfg);
        let entry_points = contract_methods
            .iter()
            .filter_map(
                |(def_id, attr)| {
                    if attr.visible {
                        Some(def_id)
                    } else {
                        None
                    }
                },
            )
            .collect::<Vec<_>>();
        cfg_builder.build(entry_points.as_slice());

        if let Some(ref cfg_path) = self.cfg_path {
            if let Err(err) = fwd_cfg.dump(cfg_path.as_path(), entry_points.len()) {
                error!("unable to dump the call graph due to: `{:?}`", err);
            }
        }

        // In world of Liquid, contract must contain at least one public contract method
        // and one constructor, and all of them are member function of `Storage` struct
        // type, so here we directly check the type of `Self` of first contract method to
        // get type definition of `Storage`. Under the guarantee of de Liquid, we needn't
        // worry error about out of bound.
        let storage_ty = fwd_cfg
            .get_method_by_def_id(*entry_points[0])
            .self_ty
            .unwrap();

        self.type_check(tcx, &fwd_cfg, storage_ty, compiler);

        let constructor = entry_points
            .iter()
            .enumerate()
            .filter_map(|(i, def_id)| {
                let info = &contract_methods[def_id];
                if info.mutable && info.visible && info.name == "new" {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        debug_assert!(constructor.len() == 1);
        let constructor = constructor[0];
        self.analyze_uninitialized_states(tcx, constructor, &fwd_cfg, storage_ty, compiler);

        let (mut_methods, imm_methods): (Vec<_>, Vec<_>) = entry_points
            .iter()
            .enumerate()
            .filter(|(_, def_id)| {
                let info = &contract_methods[def_id];
                info.visible && info.name != "new"
            })
            .partition_map(|(i, def_id)| {
                let info = &contract_methods[def_id];
                if info.mutable {
                    Either::Left(i)
                } else {
                    Either::Right(i)
                }
            });
        self.detect_mutable_invocations(tcx, &fwd_cfg, imm_methods, &external_methods, compiler);
        self.analyze_conflict_fields(&mut_methods, &external_methods, tcx, &fwd_cfg, storage_ty);
    }

    fn collect_method_attrs<'tcx>(
        tcx: TyCtxt<'tcx>,
    ) -> (HashMap<DefId, MethodAttr>, HashMap<DefId, MethodAttr>) {
        let mut contract_methods = HashMap::new();
        let mut external_methods = HashMap::new();

        for local_def_id in tcx.body_owners() {
            let def_id = local_def_id.to_def_id();
            match Self::get_method_info(tcx, def_id) {
                Some(Left(method_info)) => {
                    debug!("found contract method: {:?}", def_id);
                    contract_methods.insert(def_id, method_info);
                }
                Some(Right(method_info)) => {
                    debug!("found external method: {:?}", def_id);
                    external_methods.insert(def_id, method_info);
                }
                _ => (),
            }
        }
        (contract_methods, external_methods)
    }

    fn get_method_info<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
    ) -> Option<Either<MethodAttr, MethodAttr>> {
        let def_ty = tcx.type_of(def_id);
        let ty_kind = def_ty.kind().clone();
        if !matches!(ty_kind, TyKind::FnDef(..)) {
            return None;
        }
        // `Body` is the lowered representation of a single function.
        let body = tcx.optimized_mir(def_id);
        let parent_id = tcx.parent(def_id);
        if parent_id.is_none() {
            return None;
        }
        let parent_id = parent_id.unwrap();
        let parent_kind = tcx.def_kind(parent_id);
        if parent_kind != DefKind::Impl {
            return None;
        }
        if tcx.impl_trait_ref(parent_id).is_some() {
            return None;
        }
        let name = String::from(tcx.item_name(def_id).as_str().deref());
        if name.starts_with("__liquid") {
            return None;
        }
        let parent_type = tcx.type_of(parent_id);
        if let TyKind::Adt(adt_def, ..) = parent_type.kind() {
            let def_path_suffix = tcx
                .def_path(adt_def.did)
                .data
                .iter()
                .rev()
                .take(3)
                .filter_map(|disambiguated_def_path_data| {
                    if let DefPathData::TypeNs(symbol) = disambiguated_def_path_data.data {
                        Some(symbol.as_str())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let is_mutable = |body: &Body<'tcx>| {
                let arg_count = body.arg_count;
                debug_assert!(arg_count >= 1);
                let local_decls = &body.local_decls;
                // `_0` is the return value, `_1` is the first argument.
                let receiver = &local_decls[Local::from_usize(1)];
                if let Some(box LocalInfo::User(ClearCrossCrate::Set(BindingForm::ImplicitSelf(
                    self_kind,
                )))) = &receiver.local_info
                {
                    match self_kind {
                        ImplicitSelfKind::MutRef => true,
                        _ => false,
                    }
                } else {
                    false
                }
            };
            if def_path_suffix == STORAGE_NS {
                let visible = tcx.visibility(def_id) == Visibility::Public;
                let mutable = is_mutable(body);
                return Some(Left(MethodAttr {
                    mutable,
                    visible,
                    name,
                }));
            }
            if def_path_suffix == INTERFACE_NS && name != "at" {
                let mutable = is_mutable(body);
                return Some(Right(MethodAttr {
                    mutable,
                    visible: true,
                    name,
                }));
            }
        }
        None
    }
}
