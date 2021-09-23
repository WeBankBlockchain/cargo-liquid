use crate::{
    control_flow::{utils, ForwardCFG, InterproceduralCFG, Method, MethodIndex},
    known_names::KnownNames,
};
use either::*;
use log::*;
use petgraph::graph::{DiGraph, NodeIndex};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlockData, Local, LocalDecls, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
    TerminatorKind, RETURN_PLACE,
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use std::{
    collections::{HashMap, HashSet, LinkedList},
    fmt::Debug,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ConstraintKind {
    /// E.g., `a = &b`.
    AddrOf,
    /// E.g., `a = b`.
    Copy,
    /// E.g., `a = *b`.
    Load,
    /// E.g., `*a = b`.
    Store,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Location<'tcx> {
    pub def_id: DefId,
    pub place: Place<'tcx>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct StateVariable(pub usize);

#[derive(Copy, Clone, Debug)]
pub struct Constraint<'tcx> {
    kind: ConstraintKind,
    tgt: Location<'tcx>,
    src: Either<Location<'tcx>, StateVariable>,
}

#[derive(PartialEq, Eq, Hash)]
struct CallSite {
    caller: MethodIndex,
    node: NodeIndex,
    callee: MethodIndex,
}

pub struct AndersonPFG<'cfg, 'tcx> {
    tcx: TyCtxt<'tcx>,
    cfg: &'cfg ForwardCFG<'tcx>,
    points_to: HashMap<Location<'tcx>, HashSet<Either<Location<'tcx>, StateVariable>>>,
    constraint_graph: DiGraph<Location<'tcx>, ()>,
    sv_tys: HashSet<Ty<'tcx>>,
    constraints: Vec<Constraint<'tcx>>,
    loc_to_index: HashMap<Location<'tcx>, NodeIndex>,
    tmp_var_id: usize,
    indirect_call_args: HashMap<DefId, HashMap<Local, Vec<Method<'tcx>>>>,
    visited: HashSet<CallSite>,
}

impl<'cfg, 'tcx> AndersonPFG<'cfg, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, cfg: &'cfg ForwardCFG<'tcx>, storage_ty: Ty<'tcx>) -> Self {
        let mut sv_tys = HashSet::new();
        if let TyKind::Adt(adt_def, substs) = storage_ty.kind() {
            adt_def.all_fields().for_each(|field_def| {
                let field_ty = field_def.ty(tcx, substs);
                sv_tys.insert(field_ty);
            });
        } else {
            unreachable!("`Storage` should be a struct type");
        }

        Self {
            tcx,
            cfg,
            points_to: Default::default(),
            constraint_graph: Default::default(),
            sv_tys,
            constraints: Default::default(),
            loc_to_index: Default::default(),
            tmp_var_id: 0,
            indirect_call_args: Default::default(),
            visited: Default::default(),
        }
    }

    pub fn build(&mut self, entry_point: MethodIndex) {
        let entrance = self.cfg.get_method_by_index(entry_point);
        self.collect_constraints(entrance);
        debug!("constraints collected for entrance: {:?}", entrance);
        for constraint in &self.constraints {
            debug!(
                "{:?} <- {:?} {:?}",
                constraint.tgt, constraint.src, constraint.kind
            );
        }
        self.solve_constraints();
        debug!("points-to sets:");
        for (loc, set) in &self.points_to {
            debug!(
                "{:?}: [{}]",
                loc,
                set.iter()
                    .map(|tgt| match tgt {
                        Either::Left(loc) => {
                            format!("{:?}", loc)
                        }
                        Either::Right(sv) => {
                            format!("{:?}", sv)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }

    pub fn get_points_to(
        &self,
        def_id: DefId,
        place: Place<'tcx>,
    ) -> Option<&HashSet<Either<Location<'tcx>, StateVariable>>> {
        self.points_to.get(&Location { def_id, place })
    }

    fn collect_constraints(&mut self, method: &Method<'tcx>) {
        debug!("collect_constraints for method: `{:?}`", method);
        let nodes = self.cfg.get_nodes_of(method);
        let def_id = method.def_id;
        let body = self.tcx.optimized_mir(def_id);
        let basic_blocks = body.basic_blocks();
        let local_decls = &body.local_decls;
        self.tmp_var_id = body.local_decls.len();

        let indirect_call_args = self.indirect_call_args.entry(def_id).or_default();
        for call_site in self.cfg.get_call_sites_within(method) {
            let bdd = &basic_blocks[call_site.basic_block.unwrap()];
            let terminator = bdd.terminator();
            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let func_ty = func.ty(local_decls, self.tcx);
                if let TyKind::FnDef(def_id, ..) = func_ty.kind() {
                    if matches!(
                        KnownNames::get(self.tcx, *def_id),
                        KnownNames::CoreOpsFunctionFnCall
                            | KnownNames::CoreOpsFunctionFnCallMut
                            | KnownNames::CoreOpsFunctionFnOnceCallOnce
                    ) {
                        let arg_local = match args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        let callees = self.cfg.get_callees_of_call_at(call_site);
                        indirect_call_args.insert(
                            arg_local,
                            callees
                                .iter()
                                .map(|method| (*method).clone())
                                .collect::<Vec<_>>(),
                        );
                    }
                }
            }
        }

        for node in nodes {
            if node.basic_block.is_none() {
                continue;
            }
            let basic_block_data = &basic_blocks[node.basic_block.unwrap()];
            let BasicBlockData {
                ref statements,
                ref terminator,
                ..
            } = basic_block_data;

            if self.cfg.is_call(&node) {
                let callees = self.cfg.get_callees_of_call_at(&node);
                for callee in callees {
                    if utils::is_special_method(self.tcx, callee.def_id).is_some() {
                        continue;
                    }

                    let terminator = terminator.as_ref().unwrap();
                    if let TerminatorKind::Call {
                        args, destination, ..
                    } = &terminator.kind
                    {
                        self.collect_constraints_for_call(
                            callee,
                            def_id,
                            &args,
                            destination.and_then(|dest| Some(dest.0)),
                        );
                    } else {
                        unreachable!("terminator kind of calling node should be `Call`");
                    }

                    let call_site = CallSite {
                        caller: self.cfg.get_method_index(method),
                        node: self.cfg.node_to_index[node],
                        callee: self.cfg.get_method_index(callee),
                    };
                    if !self.visited.contains(&call_site) {
                        self.visited.insert(call_site);
                        self.collect_constraints(callee);
                    }
                }
            } else {
                for statement in statements {
                    self.collect_constraints_for_stmt(method, statement);
                }
            }
        }
    }

    fn is_related_to_sv(&self, ty: Ty<'tcx>) -> bool {
        let ret = match ty.kind() {
            TyKind::Ref(_, ty, _) => self.is_related_to_sv(ty),
            TyKind::RawPtr(type_and_mut) => self.is_related_to_sv(type_and_mut.ty),
            _ => self.sv_tys.contains(&ty),
        };
        ret
    }

    fn collect_constraints_for_call(
        &mut self,
        callee: &Method<'tcx>,
        caller_id: DefId,
        args: &[Operand<'tcx>],
        dest: Option<Place<'tcx>>,
    ) {
        let mut skip_arg_prop = false;
        if args.len() == 2 {
            match &args[1] {
                Operand::Move(place) | Operand::Copy(place) => {
                    let arg_local = place.local;
                    if self.indirect_call_args[&caller_id].contains_key(&arg_local) {
                        skip_arg_prop = true;
                    }
                }
                _ => (),
            }
        }

        let callee_id = callee.def_id;
        let callee_body = self.tcx.optimized_mir(callee_id);
        if !skip_arg_prop {
            let callee_args = callee_body.args_iter();
            let callee_local_decls = &callee_body.local_decls;
            args.iter()
                .zip(callee_args)
                .for_each(|(actual_arg, param_arg)| {
                    let param_ty = callee_local_decls[param_arg].ty;
                    let param_ty = self.concrete_ty(param_ty, callee);
                    if !self.is_related_to_sv(param_ty) {
                        return;
                    }

                    let l_place = Place {
                        local: param_arg,
                        projection: self.tcx.intern_place_elems(&[]),
                    };
                    let l_loc = Location {
                        def_id: callee_id,
                        place: l_place,
                    };
                    match actual_arg {
                        Operand::Copy(r_place) | Operand::Move(r_place) => {
                            let r_loc = Location {
                                def_id: caller_id,
                                place: *r_place,
                            };
                            self.constraints.push(Constraint {
                                kind: ConstraintKind::Copy,
                                tgt: l_loc,
                                src: Either::Left(r_loc),
                            });
                        }
                        _ => (),
                    }
                });
        }

        let return_ty = callee_body.return_ty();
        let return_ty = self.concrete_ty(return_ty, callee);
        if self.is_related_to_sv(return_ty) {
            if let Some(l_place) = dest {
                let l_loc = Location {
                    def_id: caller_id,
                    place: l_place,
                };

                let r_place = Place {
                    local: RETURN_PLACE,
                    projection: self.tcx.intern_place_elems(&[]),
                };
                let r_loc = Location {
                    def_id: callee_id,
                    place: r_place,
                };

                self.constraints.push(Constraint {
                    kind: ConstraintKind::Copy,
                    tgt: l_loc,
                    src: Either::Left(r_loc),
                });
            } else {
                unreachable!("state variable related return value must have a return destination");
            }
        }
    }

    fn expand_place(&mut self, place: Place<'tcx>, def_id: DefId) -> Place<'tcx> {
        if place.projection.len() <= 1 {
            return place;
        }

        let mut curr_place = Place {
            local: place.local,
            projection: self.tcx.intern_place_elems(&[]),
        };
        let (_, outermost_place_elem) = place.as_ref().last_projection().unwrap();

        for (_, place_elem) in place.iter_projections().take(place.projection.len() - 1) {
            assert!(place_elem == PlaceElem::Deref);
            let tmp_place = Place {
                local: Local::from_usize(self.tmp_var_id),
                projection: self.tcx.intern_place_elems(&[]),
            };
            self.tmp_var_id += 1;
            self.constraints.push(Constraint {
                kind: ConstraintKind::Load,
                tgt: Location {
                    def_id,
                    place: tmp_place,
                },
                src: Either::Left(Location {
                    def_id,
                    place: curr_place,
                }),
            });
            curr_place = tmp_place;
        }
        Place {
            local: curr_place.local,
            projection: self.tcx.intern_place_elems(&[outermost_place_elem]),
        }
    }

    fn recognize_ref(
        &mut self,
        l_place: Place<'tcx>,
        r_place: &Place<'tcx>,
        def_id: DefId,
        local_decls: &LocalDecls<'tcx>,
    ) {
        if let Some((place_ref, place_elem)) = r_place.as_ref().last_projection() {
            if place_elem == PlaceElem::Deref {
                let r_place = Place {
                    local: place_ref.local,
                    projection: self.tcx.intern_place_elems(place_ref.projection),
                };
                self.recognize_assign(l_place, &r_place, def_id);
            } else {
                let src = if self.sv_tys.contains(&r_place.ty(local_decls, self.tcx).ty) {
                    if let PlaceElem::Field(field, _) = place_elem {
                        Either::Right(StateVariable(field.index()))
                    } else {
                        unreachable!("should use an index to visit a certain state variable");
                    }
                } else {
                    Either::Left(Location {
                        def_id,
                        place: *r_place,
                    })
                };
                self.constraints.push(Constraint {
                    kind: ConstraintKind::AddrOf,
                    tgt: Location {
                        def_id,
                        place: l_place,
                    },
                    src,
                });
            }
        } else {
            let r_place = self.expand_place(*r_place, def_id);
            self.constraints.push(Constraint {
                kind: ConstraintKind::AddrOf,
                tgt: Location {
                    def_id,
                    place: l_place,
                },
                src: Either::Left(Location {
                    def_id,
                    place: r_place,
                }),
            });
        }
    }

    fn recognize_assign(&mut self, l_place: Place<'tcx>, r_place: &Place<'tcx>, def_id: DefId) {
        debug_assert!(l_place.projection.len() == 0);
        let r_place = self.expand_place(*r_place, def_id);
        if let Some((place_ref, place_elem)) = r_place.as_ref().last_projection() {
            if place_elem == PlaceElem::Deref {
                let r_place = Place {
                    local: place_ref.local,
                    projection: self.tcx.intern_place_elems(place_ref.projection),
                };
                self.constraints.push(Constraint {
                    kind: ConstraintKind::Load,
                    tgt: Location {
                        def_id,
                        place: l_place,
                    },
                    src: Either::Left(Location {
                        def_id,
                        place: r_place,
                    }),
                });
            } else {
                self.constraints.push(Constraint {
                    kind: ConstraintKind::Copy,
                    tgt: Location {
                        def_id,
                        place: l_place,
                    },
                    src: Either::Left(Location {
                        def_id,
                        place: r_place,
                    }),
                });
            }
        } else {
            self.constraints.push(Constraint {
                tgt: Location {
                    def_id,
                    place: l_place,
                },
                kind: ConstraintKind::Copy,
                src: Either::Left(Location {
                    def_id,
                    place: r_place,
                }),
            });
        }
    }

    fn collect_constraints_for_stmt(&mut self, method: &Method<'tcx>, stmt: &Statement<'tcx>) {
        let def_id = method.def_id;
        let local_decls = &self.tcx.optimized_mir(def_id).local_decls;
        let kind = &stmt.kind;
        match kind {
            StatementKind::Assign(box (l_place, r_value)) => {
                let ty = r_value.ty(local_decls, self.tcx);
                let ty = self.concrete_ty(ty, method);
                if !self.is_related_to_sv(ty) {
                    return;
                }

                let l_place = self.expand_place(*l_place, def_id);
                if let Some((place_ref, place_elem)) = l_place.as_ref().last_projection() {
                    if place_elem == PlaceElem::Deref {
                        let l_place = Place {
                            local: place_ref.local,
                            projection: self.tcx.intern_place_elems(place_ref.projection),
                        };
                        if let Rvalue::Use(r_operand) = r_value {
                            match r_operand {
                                Operand::Copy(r_place) | Operand::Move(r_place) => {
                                    let r_place = self.expand_place(*r_place, def_id);
                                    self.constraints.push(Constraint {
                                        kind: ConstraintKind::Store,
                                        tgt: Location {
                                            def_id,
                                            place: l_place,
                                        },
                                        src: Either::Left(Location {
                                            def_id,
                                            place: r_place,
                                        }),
                                    });
                                    return;
                                }
                                _ => todo!("unexpected kind of right operand: {:?}", r_operand),
                            }
                        } else {
                            todo!("unexpected kind of right value: {:?}", r_value);
                        }
                    }
                }

                match r_value {
                    Rvalue::Use(r_operand) => match r_operand {
                        Operand::Copy(r_place) | Operand::Move(r_place) => {
                            if let Some(callees) =
                                self.indirect_call_args[&def_id].get(&l_place.local)
                            {
                                debug_assert!(l_place.projection.len() == 1);
                                for callee in callees {
                                    if let PlaceElem::Field(field, _) = l_place.projection[0] {
                                        let field = field.as_usize();
                                        let l_loc = Location {
                                            def_id: callee.def_id,
                                            place: Place {
                                                // `_0` is return value, while `_1` is reference of
                                                // closure object.
                                                local: Local::from_usize(field + 2),
                                                projection: self.tcx.intern_place_elems(&[]),
                                            },
                                        };
                                        let r_loc = Location {
                                            def_id,
                                            place: *r_place,
                                        };
                                        self.constraints.push(Constraint {
                                            kind: ConstraintKind::Copy,
                                            tgt: l_loc,
                                            src: Either::Left(r_loc),
                                        });
                                    } else {
                                        unreachable!()
                                    }
                                }
                            } else {
                                self.recognize_assign(l_place, r_place, def_id);
                            }
                        }
                        _ => todo!("unexpected kind of right operand: {:?}", r_operand),
                    },
                    Rvalue::Ref(_, _, r_place) => {
                        self.recognize_ref(l_place, r_place, def_id, local_decls);
                    }
                    Rvalue::AddressOf(_, r_place) => {
                        self.recognize_ref(l_place, r_place, def_id, local_decls);
                    }
                    _ => (),
                }
            }
            _ => (),
        }
    }

    fn insert_constraint_node(&mut self, loc: &Location<'tcx>) {
        if !self.loc_to_index.contains_key(loc) {
            let loc = *loc;
            let index = self.constraint_graph.add_node(loc);
            self.loc_to_index.insert(loc, index);
        }
    }

    fn solve_constraints(&mut self) {
        let mut work_list = LinkedList::new();

        let mut constraints = vec![];
        std::mem::swap(&mut constraints, &mut self.constraints);
        for constraint in &constraints {
            let src = constraint.src;
            if let Either::Left(loc) = src {
                self.insert_constraint_node(&loc);
            }
            let tgt = constraint.tgt;
            self.insert_constraint_node(&tgt);
            match constraint.kind {
                ConstraintKind::AddrOf => {
                    let pts = self.points_to.get_mut(&tgt);
                    if pts.is_none() {
                        let mut pts = HashSet::new();
                        pts.insert(src);
                        self.points_to.insert(tgt, pts);
                        work_list.push_back(tgt);
                    } else {
                        let pts = pts.unwrap();
                        pts.insert(src);
                    }
                }
                ConstraintKind::Copy => {
                    let src_index = if let Either::Left(loc) = src {
                        self.loc_to_index[&loc]
                    } else {
                        unreachable!("state variables should not appear in copy constraint")
                    };
                    let tgt_index = self.loc_to_index[&tgt];
                    self.constraint_graph.add_edge(src_index, tgt_index, ());
                }
                _ => (),
            }
        }

        while !work_list.is_empty() {
            let node = work_list.pop_front().unwrap();
            let pts = &self.points_to[&node];
            for point_to in pts {
                for constraint in &constraints {
                    if constraint.kind == ConstraintKind::Load
                        && Either::Left(node) == constraint.src
                    {
                        let pt_loc = if let Either::Left(loc) = point_to {
                            loc
                        } else {
                            unreachable!("state variables should not appear in load constraint")
                        };
                        let tgt = constraint.tgt;
                        let tgt_index = self.loc_to_index[&tgt];
                        let src_index = self.loc_to_index[pt_loc];
                        if !self.constraint_graph.contains_edge(src_index, tgt_index) {
                            self.constraint_graph.add_edge(src_index, tgt_index, ());
                            work_list.push_back(*pt_loc);
                        }
                    } else if constraint.kind == ConstraintKind::Store && node == constraint.tgt {
                        let pt_loc = if let Either::Left(loc) = point_to {
                            loc
                        } else {
                            unreachable!("state variables should not appear in store constraint")
                        };

                        let src = constraint.src;
                        let src_loc = if let Either::Left(loc) = src {
                            loc
                        } else {
                            unreachable!("state variables should not appear in store constraint")
                        };

                        let src_index = self.loc_to_index[&src_loc];
                        let tgt_index = self.loc_to_index[pt_loc];
                        if !self.constraint_graph.contains_edge(src_index, tgt_index) {
                            self.constraint_graph.add_edge(src_index, tgt_index, ());
                            work_list.push_back(src_loc);
                        }
                    }
                }
            }

            let node_index = self.loc_to_index[&node];
            let src_pts = self.points_to.entry(node).or_default().clone();
            for edge in self.constraint_graph.raw_edges().iter() {
                if edge.source() == node_index {
                    let tgt_index = edge.target();
                    let tgt = self.constraint_graph.node_weight(tgt_index).unwrap();
                    let tgt_pts = self.points_to.entry(*tgt).or_default();
                    let old_size = tgt_pts.len();

                    for point_to in src_pts.iter() {
                        tgt_pts.insert(*point_to);
                    }

                    if tgt_pts.len() != old_size {
                        work_list.push_back(*tgt);
                    }
                }
            }
        }
    }

    fn concrete_ty(&self, ty: Ty<'tcx>, method: &Method<'tcx>) -> Ty<'tcx> {
        if utils::is_concrete(ty.kind()) {
            ty
        } else {
            let generic_args_map =
                utils::generate_generic_args_map(self.tcx, method.def_id, method.substs);
            utils::specialize_type_generic_arg(self.tcx, ty, &generic_args_map)
        }
    }
}
