use crate::control_flow::InterproceduralCFG;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    iter::FromIterator,
};

pub type FlowFunction<'a, Fact> = Box<dyn Fn(&Fact) -> HashSet<Fact> + 'a>;

pub trait IfdsProblem<'fact> {
    type Icfg: InterproceduralCFG;
    /// `Fact` represents logical statement, such as "variable `v` has definitely
    /// been initialized".
    type Fact: Eq + Hash + Clone + Debug;

    /// This must be a data-flow fact of type `Fact`, but must **NOT** be
    /// part of the domain of data-flow facts. Typically this will be a
    /// singleton object of type `Fact` that is used for nothing else. It
    /// must holds that this object does not equals any object
    /// within the domain.
    ///
    /// ## Note
    /// This method could be called many times. Implementations of this
    /// interface should therefore cache the return value!
    fn zero_value() -> Self::Fact;

    /// Returns initial seeds to be used for the analysis. This is a mapping
    /// of nodes to initial analysis facts.
    fn initial_seeds(
        &mut self,
    ) -> HashMap<<Self::Icfg as InterproceduralCFG>::Node, HashSet<Self::Fact>>;

    /// Returns the flow function that computes the flow for a call statement.
    ///
    /// ## Parameters
    /// - `call_site`: The node containing the invoke expression giving rise to
    ///   this call;
    /// - `callee`: The concrete target method for which the flow is computed.
    fn get_call_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
    ) -> FlowFunction<'fact, Self::Fact>;

    /// Returns the flow function that computes the flow for a an exit from a
    /// method. An exit can be a return or an exceptional exit.
    ///
    /// ## Parameters
    /// - `call_site`: One of all the call sites in the program that called the
    ///   method from which the `exit_site` is actually returning. This information
    ///   can be exploited to compute a value that depends on information from
    ///   before the call.
    /// - `callee`: The method from which exitStmt returns.
    /// - `exit_site`: The node exiting the method, typically a basic with return or
    ///   abort terminator.
    /// - `return_site`: One of the successor node of the `call_site`. There may be
    ///   multiple successors in case of possible exceptional flow. This
    ///   method will be called for each such successor.
    fn get_return_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
        exit_site: &<Self::Icfg as InterproceduralCFG>::Node,
        return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'fact, Self::Fact>;

    /// Returns the flow function that computes the flow for a normal node,
    /// the "normal" means that this node doesn't have a call or exit outgoing
    /// edge.
    ///
    /// ## Parameters
    /// - `curr`: The current node.
    fn get_normal_flow_function(
        &mut self,
        curr: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'fact, Self::Fact>;

    /// Returns the flow function that computes the flow from a call site to a
    /// successor statement just after the call. There may be multiple successors
    /// in case of exceptional control flow. In this case this method will be
    /// called for every such successor.
    ///
    /// ## Parameters
    /// - `call_site`: The node containing the invoke expression giving rise to
    ///   this call.
    /// - `return_site`: The return site to which the information is propagated.
    ///   For exceptional flow, this may actually be the start of an exception
    ///   handler, e.g. stack unwind basic block in MIR.
    fn get_call_to_return_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'fact, Self::Fact>;

    fn empty() -> FlowFunction<'fact, Self::Fact> {
        Box::new(|_fact: &Self::Fact| HashSet::new())
    }

    fn identity() -> FlowFunction<'fact, Self::Fact> {
        Box::new(|fact: &Self::Fact| HashSet::from_iter([fact.clone()]))
    }
}
