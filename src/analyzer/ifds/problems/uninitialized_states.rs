use crate::{
    control_flow::{AndersonPFG, ForwardCFG, InterproceduralCFG, MethodIndex},
    ifds::problem::{FlowFunction, IfdsProblem},
    known_names::KnownNames,
};
use either::*;
use log::*;
use rustc_middle::{
    mir::{BasicBlockData, Operand, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};
use std::fmt::Display;


pub struct UninitializedStates<'tcx, 'icfg> {
    tcx: TyCtxt<'tcx>,
    fields_count: usize,
    icfg: &'icfg ForwardCFG<'tcx>,
    pub pfg: AndersonPFG<'icfg, 'tcx>,
    constructor: MethodIndex,
}

impl<'tcx, 'icfg> UninitializedStates<'tcx, 'icfg> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        icfg: &'icfg ForwardCFG<'tcx>,
        constructor: MethodIndex,
        storage_ty: Ty<'tcx>,
    ) -> Self {
        if let TyKind::Adt(adt_def, _) = storage_ty.kind() {
            debug_assert!(adt_def.is_struct());
            let fields_count = adt_def.all_fields().count();
            let mut pfg = AndersonPFG::new(tcx, icfg, storage_ty);
            pfg.build(constructor);
            Self {
                tcx,
                fields_count,
                icfg,
                pfg,
                constructor,
            }
        } else {
            unreachable!("`Storage` should be a struct type")
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum UninitializedState {
    Zero,
    Field(usize),
}

impl<'tcx, 'graph> IfdsProblem<'tcx> for UninitializedStates<'tcx, 'graph> {
    type Icfg = ForwardCFG<'tcx>;
    type Fact = UninitializedState;

    fn zero_value() -> Self::Fact {
        UninitializedState::Zero
    }

    fn initial_seeds(
        &mut self,
    ) -> HashMap<<Self::Icfg as InterproceduralCFG>::Node, HashSet<Self::Fact>> {
        let constructor = self.icfg.get_method_by_index(self.constructor);
        let start_points = self.icfg.get_start_points_of(constructor);
        let mut initial_seeds: HashMap<_, _> = Default::default();
        let mut facts = HashSet::from_iter([Self::zero_value()]);
        for index in 0..self.fields_count {
            facts.insert(UninitializedState::Field(index));
        }
        for start_point in start_points {
            initial_seeds.insert(*start_point, facts.clone());
        }
        initial_seeds
    }

    fn get_call_flow_function(
        &mut self,
        _call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _callee: &<Self::Icfg as InterproceduralCFG>::Method,
    ) -> FlowFunction<'tcx, Self::Fact> {
        Self::identity()
    }

    fn get_return_flow_function(
        &mut self,
        _call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _callee: &<Self::Icfg as InterproceduralCFG>::Method,
        _exit_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'tcx, Self::Fact> {
        Self::identity()
    }

    fn get_normal_flow_function(
        &mut self,
        curr: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'tcx, Self::Fact> {
        if curr.basic_block.is_none() {
            return Self::identity();
        }

        if self.icfg.is_call(curr) {
            let curr_method = self.icfg.get_method_by_index(curr.belongs_to);
            let body = self.tcx.optimized_mir(curr_method.def_id);
            let basic_block = curr.basic_block.unwrap();
            let bbd = &body.basic_blocks[basic_block];
            let BasicBlockData { terminator, .. } = bbd;
            let terminator = terminator.as_ref().unwrap();

            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let local_decls = &body.local_decls;
                let callee_ty = func.ty(local_decls, self.tcx);
                if let TyKind::FnDef(def_id, ..) = callee_ty.kind() {
                    if matches!(
                        KnownNames::get(self.tcx, *def_id),
                        KnownNames::LiquidStorageCollectionsMappingInitialize
                            | KnownNames::LiquidStorageCollectionsVecInitialize
                            | KnownNames::LiquidStorageValueInitialize
                            | KnownNames::LiquidStorageCollectionsIterableMappingInitialize
                    ) {
                        let receiver = &args[0];
                        let points_to = self.pfg.get_points_to(
                            curr_method.def_id,
                            match receiver {
                                // The receiver of initializing function must be a mutable reference
                                // of a certain state variable, and in Rust mutable reference doesn't
                                // implements `Copy` and `Clone` semantic, so it must be a `Move` here.
                                Operand::Move(place) => *place,
                                _ => unreachable!(),
                            },
                        );
                        if let Some(points_to) = points_to {
                            if points_to.len() == 1 {
                                let target = points_to.iter().take(1).next().unwrap();
                                if let Either::Right(state_variable) = target {
                                    let field = state_variable.0;
                                    return Box::new(move |fact: &Self::Fact| {
                                        if fact == &UninitializedState::Field(field) {
                                            HashSet::new()
                                        } else {
                                            HashSet::from_iter([fact.clone()])
                                        }
                                    });
                                }
                            }
                            // Maybe this receiver is a phi node of some nodes previous, and it's
                            // possible that not all branches would be executed during the practical
                            // execution, hence we conservatively keep all uninitialized state variables
                            // still being uninitialized.
                            Self::identity()
                        } else {
                            // Sadly the points-to analyzer can not analysis the points-to set of this
                            // receiver due to some reason, we can do nothing but just report this issue.
                            warn!(
                                "unable to get points-to set of `{:?}` in `{:?}`, this is always \
                                 caused by some internal bugs, please report this issue in \
                                 https://github.com/WeBankBlockchain/liquid/issues",
                                receiver.place().unwrap(),
                                self.icfg.get_method_of(curr)
                            );
                            Self::identity()
                        }
                    } else {
                        Self::identity()
                    }
                } else {
                    Self::identity()
                }
            } else {
                unreachable!("the kind of terminator of call node must be `Call`")
            }
        } else {
            Self::identity()
        }
    }

    fn get_call_to_return_flow_function(
        &mut self,
        _call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'tcx, Self::Fact> {
        // The state variables may be initialized in other functions, if we merge the result coming
        // from other functions with facts we have seen in current context, the final result will
        // be misleading.
        Self::empty()
    }
}
