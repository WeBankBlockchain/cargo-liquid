use crate::control_flow::{InterproceduralCFG, Method};
use crate::ifds::problem::{FlowFunction, IfdsProblem};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

pub struct UninitializedStates;

#[derive(PartialEq, Eq, Hash, Copy, Clone)]
pub struct StateVariable {
    index: i32,
}

impl IfdsProblem for UninitializedStates {
    type Fact = StateVariable;

    fn zero_value() -> Self::Fact {
        StateVariable { index: -1 }
    }

    fn initial_seeds<Icfg>(
        &self,
        icfg: &Icfg,
        entrance: &Icfg::Method,
    ) -> HashMap<Icfg::Node, HashSet<Self::Fact>>
    where
        Icfg: InterproceduralCFG,
    {
        let start_points = icfg.get_start_points_of(entrance);
        let mut initial_seeds: HashMap<_, _> = Default::default();
        for start_point in start_points {
            initial_seeds.insert(*start_point, HashSet::from_iter([Self::zero_value()]));
        }
        initial_seeds
    }

    fn get_call_flow_function<Node, Method>(
        &self,
        call_site: &Node,
        callee: &Method,
    ) -> FlowFunction<Self::Fact> {
        todo!();
    }

    fn get_return_flow_function<Node, Method>(
        &self,
        call_site: &Node,
        callee: &Method,
        exit_site: &Node,
        return_site: &Node,
    ) -> FlowFunction<Self::Fact> {
        todo!();
    }

    fn get_normal_flow_function<Node>(&self, curr: &Node, succ: &Node) -> FlowFunction<Self::Fact> {
        todo!();
    }

    fn get_call_to_return_flow_function<Node>(
        &self,
        call_site: &Node,
        return_site: &Node,
    ) -> FlowFunction<Self::Fact> {
        todo!();
    }
}
