use crate::control_flow::{AndersonPFG, BackwardCFG, InterproceduralCFG, MethodIndex};
use crate::ifds::problem::{FlowFunction, IfdsProblem};
use crate::known_names::KnownNames;
use either::*;
#[allow(unused_imports)]
use log::*;
use rustc_middle::{
    mir::{
        BasicBlockData, BorrowKind, Local, Operand, Rvalue, StatementKind, TerminatorKind,
        RETURN_PLACE,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::DefId;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

pub struct ConflictFields<'tcx, 'graph> {
    tcx: TyCtxt<'tcx>,
    icfg: &'graph BackwardCFG<'graph, 'tcx>,
    pfg: AndersonPFG<'graph, 'tcx>,
    entry_point: MethodIndex,
}

impl<'tcx, 'graph> ConflictFields<'tcx, 'graph> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        icfg: &'graph BackwardCFG<'graph, 'tcx>,
        entry_point: MethodIndex,
        storage_ty: Ty<'tcx>,
    ) -> Self {
        if let TyKind::Adt(adt_def, _) = storage_ty.kind() {
            debug_assert!(adt_def.is_struct());
            let mut pfg = AndersonPFG::new(tcx, icfg.fwd_cfg, storage_ty);
            pfg.build(entry_point);
            Self {
                tcx,
                icfg,
                pfg,
                entry_point,
            }
        } else {
            unreachable!("`Storage` should be a struct type")
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum EnvKind {
    Caller,
    Origin,
    Timestamp,
    BlockNumber,
    Address,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Key {
    Runtime,
    Len,
    Env(EnvKind),
    AccessPath(DefId, Local),
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum ConflictField {
    Zero,
    Field {
        container: usize,
        key: Key,
        read_only: bool,
    },
}

impl<'tcx, 'graph> IfdsProblem<'tcx> for ConflictFields<'tcx, 'graph> {
    type Icfg = BackwardCFG<'graph, 'tcx>;
    type Fact = ConflictField;

    fn zero_value() -> Self::Fact {
        ConflictField::Zero
    }

    fn initial_seeds(
        &self,
    ) -> HashMap<<Self::Icfg as InterproceduralCFG>::Node, HashSet<Self::Fact>> {
        let entrance = self.icfg.get_method_by_index(self.entry_point);
        let start_points = self.icfg.get_start_points_of(entrance);
        let mut initial_seeds: HashMap<_, _> = Default::default();
        for start_point in start_points {
            initial_seeds.insert(*start_point, HashSet::from_iter([Self::zero_value()]));
        }
        initial_seeds
    }

    fn get_call_flow_function(
        &self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
    ) -> FlowFunction<Self::Fact> {
        if call_site.basic_block.is_none() {
            return Self::identity();
        }

        let caller = self.icfg.get_method_by_index(call_site.belongs_to);
        let basic_block = call_site.basic_block.unwrap();
        let bbd = &self.tcx.optimized_mir(caller.def_id).basic_blocks()[basic_block];
        let terminator = bbd.terminator.as_ref().unwrap();
        let caller_id = caller.def_id;
        let callee_id = callee.def_id;

        let kind = &terminator.kind;
        if let TerminatorKind::Call {
            args, destination, ..
        } = kind
        {
            if callee.used_for_clone {
                // Maybe this callee is a implementation provided by user.
                let dst = match destination {
                    Some((place, _)) => place.local,
                    _ => unreachable!(),
                };
                let src = match &args[0] {
                    Operand::Move(place) | Operand::Copy(place) => place.local,
                    _ => unreachable!(),
                };
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if key == &Key::AccessPath(caller_id, dst) {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: Key::AccessPath(caller_id, src),
                                read_only: *read_only,
                            });
                        } else {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                    results
                });
            }

            if let Some((ret_place, _)) = destination {
                let ret_local = ret_place.local;
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    let ret_key = Key::AccessPath(caller_id, ret_local);
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if key == &ret_key {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: Key::AccessPath(callee_id, RETURN_PLACE),
                                read_only: *read_only,
                            });
                        }
                    }
                    results
                });
            } else {
                Self::empty()
            }
        } else {
            unreachable!("the kind of terminator at call site must be `Call`")
        }
    }

    fn get_return_flow_function(
        &self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
        _exit_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<Self::Fact> {
        if call_site.basic_block.is_none() {
            return Self::identity();
        }

        let caller = self.icfg.get_method_by_index(call_site.belongs_to);
        let basic_block = call_site.basic_block.unwrap();
        let call_site_bbd = &self.tcx.optimized_mir(caller.def_id).basic_blocks()[basic_block];
        let terminator = call_site_bbd.terminator.as_ref().unwrap();
        let caller_id = caller.def_id;
        let callee_id = callee.def_id;

        if let TerminatorKind::Call { args, .. } = &terminator.kind {
            let actual_args = args
                .iter()
                .map(|arg| match arg {
                    Operand::Copy(place) | Operand::Move(place) => place.local,
                    _ => todo!(),
                })
                .collect::<Vec<_>>();
            let param_args = self
                .tcx
                .optimized_mir(callee.def_id)
                .args_iter()
                .collect::<Vec<_>>();
            assert_eq!(actual_args.len(), param_args.len());

            Box::new(move |fact| {
                let mut results = HashSet::new();
                if let ConflictField::Field {
                    container,
                    key,
                    read_only,
                } = fact
                {
                    if let Key::AccessPath(callee_id, local) = key {
                        if let Some(pos) = param_args.iter().position(|arg| arg == local) {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: Key::AccessPath(caller_id, actual_args[pos]),
                                read_only: *read_only,
                            });
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                }
                results
            })
        } else {
            unreachable!("the kind of terminator at call site must be `Call`")
        }
    }

    fn get_normal_flow_function(
        &mut self,
        curr: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<Self::Fact> {
        if curr.basic_block.is_none() {
            debug!("virtual node found: {:?}", curr);
            return Self::identity();
        }

        let method = self.icfg.get_method_by_index(curr.belongs_to);
        let body = self.tcx.optimized_mir(method.def_id);
        let basic_block = curr.basic_block.unwrap();
        let bbd = &body.basic_blocks()[basic_block];
        let method_id = method.def_id;

        if self.icfg.is_call(curr) {
            let terminator = bbd.terminator.as_ref().unwrap();
            let (args, destination) = if let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
            {
                (args, destination)
            } else {
                unreachable!()
            };

            // Don't use `func` in terminator kind to get callee's name but use
            // `get_callees_of_call_at` instead, because some built-in methods(such as `index` or
            // `index_mut` in `Mapping`) are implementation of some traits, if we use `func` we may
            // get a projection which cannot be parsed by `KnownNames`.
            let callees = self.icfg.get_callees_of_call_at(curr);
            // IFDS solver guarantees:
            // 1. `get_normal_flow_function` called for a call node iif there is an invocation of
            // special method inside that node.
            // 2. the invocation of special method cannot be virtual calling.
            // If once these two rules being broken, it will cause serious bugs.
            assert!(callees.len() == 1);
            let callee = callees[0];

            if callee.used_for_clone {
                // The reason why a method used for cloning coming into this position is that
                // that method must have no MIR body.
                let dst = match destination {
                    Some((place, _)) => place.local,
                    _ => unreachable!(),
                };
                let src = match &args[0] {
                    Operand::Move(place) | Operand::Copy(place) => place.local,
                    _ => unreachable!(),
                };
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if key == &Key::AccessPath(method_id, dst) {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: Key::AccessPath(method_id, src),
                                read_only: *read_only,
                            });
                        } else {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                    results
                });
            }

            let fn_name = KnownNames::get(self.tcx, callee.def_id);
            if matches!(
                fn_name,
                KnownNames::LiquidStorageCollectionsMappingContainsKey
                    | KnownNames::LiquidStorageCollectionsMappingGet
                    | KnownNames::LiquidStorageCollectionsMappingGetMut
                    | KnownNames::LiquidStorageCollectionsMappingIndex
                    | KnownNames::LiquidStorageCollectionsMappingIndexMut
                    | KnownNames::LiquidStorageCollectionsMappingInsert
                    | KnownNames::LiquidStorageCollectionsMappingLen
            ) {
                let receiver = &args[0];
                let points_to = self.pfg.get_points_to(
                    method.def_id,
                    match receiver {
                        Operand::Move(place) => *place,
                        _ => unreachable!(),
                    },
                );

                let pts_error = format!(
                    "unable to get points-to set of `{:?}` in `{:?}`, this is always \
                        caused by some internal bugs, please report this issue in \
                        https://github.com/WeBankBlockchain/liquid/issues",
                    receiver.place().unwrap(),
                    self.icfg.get_method_of(curr)
                );
                if let Some(points_to) = points_to {
                    let mut states = vec![];
                    for point_to in points_to {
                        if let Either::Right(state) = point_to {
                            states.push(state.0);
                        } else {
                            // Sadly the points-to analyzer can not analysis the points-to set of
                            // this receiver due to some reason, we can do nothing but just report
                            // this issue.
                            //
                            // ## Note
                            // To ensure concurrent safety, we choose to panic here to prevent
                            // generating incorrect results.
                            panic!("{}", pts_error)
                        }
                    }

                    if matches!(
                        fn_name,
                        KnownNames::LiquidStorageCollectionsMappingContainsKey
                            | KnownNames::LiquidStorageCollectionsMappingGet
                            | KnownNames::LiquidStorageCollectionsMappingIndex
                    ) {
                        let local = match &args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in states {
                                    let new_fact = ConflictField::Field {
                                        container,
                                        key: Key::AccessPath(method_id, local),
                                        read_only: true,
                                    };
                                    results.insert(new_fact);
                                }
                                results
                            } else {
                                HashSet::from_iter([fact.clone()])
                            }
                        });
                    }

                    if matches!(
                        fn_name,
                        KnownNames::LiquidStorageCollectionsMappingGetMut
                            | KnownNames::LiquidStorageCollectionsMappingIndexMut
                    ) {
                        let local = match &args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in states {
                                    let new_fact = ConflictField::Field {
                                        container,
                                        key: Key::AccessPath(method_id, local),
                                        read_only: false,
                                    };
                                    results.insert(new_fact);
                                }
                                results
                            } else {
                                HashSet::from_iter([fact.clone()])
                            }
                        });
                    }

                    if matches!(fn_name, KnownNames::LiquidStorageCollectionsMappingInsert) {
                        let local = match &args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in states {
                                    results.insert(ConflictField::Field {
                                        container,
                                        key: Key::AccessPath(method_id, local),
                                        read_only: false,
                                    });
                                    results.insert(ConflictField::Field {
                                        container,
                                        key: Key::Len,
                                        read_only: false,
                                    });
                                }
                                results
                            } else {
                                HashSet::from_iter([fact.clone()])
                            }
                        });
                    }

                    if matches!(fn_name, KnownNames::LiquidStorageCollectionsMappingLen) {
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in states {
                                    results.insert(ConflictField::Field {
                                        container,
                                        key: Key::Len,
                                        read_only: true,
                                    });
                                }
                                results
                            } else {
                                HashSet::from_iter([fact.clone()])
                            }
                        });
                    }

                    // All branches must be processed.
                    unreachable!()
                } else {
                    panic!("{}", pts_error)
                }
            } else {
                Self::identity()
            }
        } else {
            let BasicBlockData { ref statements, .. } = bbd;

            let assignments = statements
                .iter()
                .filter_map(|stmt| {
                    let kind = &stmt.kind;
                    if let StatementKind::Assign(box (l_place, r_value)) = kind {
                        let r_key = match r_value {
                            Rvalue::Use(r_operand) => match r_operand {
                                Operand::Move(r_place) | Operand::Copy(r_place) => {
                                    Key::AccessPath(method_id, r_place.local)
                                }
                                // TODO: uses constant value as conflict key.
                                Operand::Constant(..) => Key::Runtime,
                            },
                            Rvalue::Ref(_, kind, r_place) => {
                                if kind == &BorrowKind::Shared {
                                    Key::AccessPath(method_id, r_place.local)
                                } else {
                                    Key::Runtime
                                }
                            }
                            _ => Key::Runtime,
                        };
                        Some((l_place.local, r_key))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            Box::new(move |fact| {
                if let ConflictField::Field {
                    container,
                    read_only,
                    ..
                } = fact
                {
                    let mut results = HashSet::from_iter([fact.clone()]);
                    for (l_local, r_key) in assignments.iter().rev() {
                        let l_field = ConflictField::Field {
                            container: *container,
                            key: Key::AccessPath(method_id, *l_local),
                            read_only: *read_only,
                        };
                        if results.remove(&l_field) {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: r_key.clone(),
                                read_only: *read_only,
                            });
                        }
                    }
                    results
                } else {
                    HashSet::new()
                }
            })
        }
    }

    fn get_call_to_return_flow_function(
        &self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<Self::Fact> {
        if call_site.basic_block.is_none() {
            return Self::identity();
        }

        let method = self.icfg.get_method_by_index(call_site.belongs_to);
        let body = self.tcx.optimized_mir(method.def_id);
        let basic_block = call_site.basic_block.unwrap();
        let bbd = &body.basic_blocks()[basic_block];
        let terminator = bbd.terminator.as_ref().unwrap();
        let method_id = method.def_id;

        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
            if let Some((ret_place, _)) = destination {
                let ret_local = ret_place.local;
                return Box::new(move |fact| {
                    let ret_key = Key::AccessPath(method_id, ret_local);
                    if let ConflictField::Field { key, .. } = fact {
                        if key == &ret_key {
                            HashSet::new()
                        } else {
                            HashSet::from_iter([fact.clone()])
                        }
                    } else {
                        HashSet::from_iter([fact.clone()])
                    }
                });
            } else {
                Self::identity()
            }
        } else {
            unreachable!("the kind of terminator at call site must be `Call`")
        }
    }
}
