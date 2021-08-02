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
    control_flow::{BackwardCFG, Builder, ForwardCFG, InterproceduralCFG, MethodIndex},
    ifds::{problems::*, IfdsSolver},
};
use either::*;
use log::*;
use rustc_driver::Compilation;
use rustc_hir::{def::DefKind, def_id::DefId, definitions::DefPathData};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{
    mir::{BindingForm, Body, ClearCrossCrate, ImplicitSelfKind, Local, LocalInfo, Mutability},
    ty::{DefIdTree, Ty, TyCtxt, TyKind, Visibility},
};
use serde::Serialize;
use std::{collections::HashMap, env, fs, ops::Deref, path::PathBuf};

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

impl AnalysisCallbacks {
    fn analyze_conflict_fields<'tcx>(
        &self,
        methods: Vec<MethodIndex>,
        tcx: TyCtxt<'tcx>,
        fwd_cfg: &ForwardCFG<'tcx>,
        storage_ty: Ty<'tcx>,
    ) {
        #[derive(Serialize, PartialOrd, Ord, PartialEq, Eq)]
        struct FieldDesc {
            /// The index of which state variable will be visited.
            slot: usize,
            /// - 0 represents `All`, which means the contract attempts to visit a container of
            /// `Value<T>` or the key for reading/writing other types of containers can not be
            /// inferred during static program analysis;
            /// - 1 represents `Len`, which means the contract may change length of some a container.
            /// It's only meaningful to containers such like `Vec<T>`, `Mapping<K, V>` or
            /// `IterableMapping<K, V>`;
            /// - 2 represents `Env`, which means the contract wants to use some values from
            /// execution context as keys to visit containers;
            /// - 3 represents `Var`, which means the contract wants to use some values from method
            /// parameters as keys to visit containers;
            /// - 4 represents `Const`, which means the contract wants to use some constant values as
            /// keys to visit containers.
            kind: u8,
            /// If `kind` equals to `All` or `Len`, then `path` must be empty;
            /// if `kind` equals to `Env`, then `path` must only contain one element, and the element
            /// represents which kind of context information the contract needs to acquire:
            ///  - 0 represents caller of transaction;
            ///  - 1 represents origin sender of transaction;
            ///  - 2 represents timestamp of current block;
            ///  - 3 represents height of current block;
            ///  - 4 represents address of current contract;
            /// if `kind` equals to `Var`, then `path` contains an access path described via integer
            /// indices, e.g., "[2, 0]" means key coming from the **1st** data member of the **2nd**
            /// parameter;
            /// if `kind` equals to `Const`, the `path` contains the **raw** bytes representation of
            /// the corresponding constant value.
            path: Vec<usize>,
            /// Whether this conflict field is used to mutably visit some a state variable.
            read_only: bool,
        }

        let target_dir = PathBuf::from(env::var("LIQUID_ANALYSIS_TARGET_DIR").unwrap());
        let bwd_cfg = BackwardCFG::new(&fwd_cfg);
        let mut field_descs = HashMap::new();

        for method_index in methods {
            let method = bwd_cfg.get_method_by_index(method_index);
            let problem = ConflictFields::new(tcx, &bwd_cfg, method_index, storage_ty);
            let mut ifds_solver = IfdsSolver::new(problem, &bwd_cfg, true);
            ifds_solver.solve();
            let end_point = bwd_cfg.get_end_points_of(method);
            debug_assert!(end_point.len() == 1);
            let end_point = end_point[0];
            let results = ifds_solver.get_results_at(end_point);

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
                            Key::All | Key::Len => (0, vec![]),
                            Key::Env(env_kind) => (
                                1,
                                vec![match env_kind {
                                    EnvKind::Caller => 0,
                                    EnvKind::Origin => 1,
                                    EnvKind::Now => 2,
                                    EnvKind::BlockNumber => 3,
                                    EnvKind::Address => 4,
                                }],
                            ),
                            Key::Var(def_id, access_path) => {
                                if def_id != &method_id {
                                    (0, vec![])
                                } else {
                                    let body = tcx.optimized_mir(method_id);
                                    let arg_count = body.arg_count;
                                    let local_decls = &body.local_decls;
                                    let base = access_path.base;
                                    if base.index() > arg_count {
                                        (0, vec![])
                                    } else {
                                        if local_decls[base].mutability == Mutability::Not {
                                            let mut path = vec![base.index() - 2];
                                            path.extend(access_path.fields.iter());
                                            (3, path)
                                        } else {
                                            (0, vec![])
                                        }
                                    }
                                }
                            }
                            Key::Const(bytes) => (
                                4,
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
            field_descs.insert(fn_name, conflict_fields);
        }

        fs::write(
            target_dir.join("conflict_fields.analysis"),
            format!("{}", serde_json::to_string(&field_descs).unwrap()),
        )
        .unwrap();
    }

    fn analyze_uninitialized_states<'tcx>(
        &self,
        constructor: MethodIndex,
        tcx: TyCtxt<'tcx>,
        fwd_cfg: &ForwardCFG<'tcx>,
        storage_ty: Ty<'tcx>,
    ) {
        let problem = UninitializedStates::new(tcx, &fwd_cfg, constructor, storage_ty);
        let mut ifds_solver = IfdsSolver::new(problem, &fwd_cfg, true);
        ifds_solver.solve();
        let constructor = fwd_cfg.get_method_by_index(constructor);
        let results = ifds_solver.get_results_at(&fwd_cfg.get_end_points_of(constructor)[0]);
        debug!("uninitialized state variables results: {:?}", results);
    }

    fn analyze_with_mir<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) {
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
        self.analyze_uninitialized_states(constructor, tcx, &fwd_cfg, storage_ty);

        let mutable_contract_methods = entry_points
            .iter()
            .enumerate()
            .filter_map(|(i, def_id)| {
                let info = &contract_methods[def_id];
                if info.mutable && info.visible && info.name != "new" {
                    Some(i)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        self.analyze_conflict_fields(mutable_contract_methods, tcx, &fwd_cfg, storage_ty);
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
            if def_path_suffix == INTERFACE_NS {
                if name != "at" {
                    let mutable = is_mutable(body);
                    return Some(Right(MethodAttr {
                        mutable,
                        visible: true,
                        name,
                    }));
                }
            }
        }
        None
    }
}
