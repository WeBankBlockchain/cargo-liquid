mod builder;
mod cfg;
mod pfg;
pub(crate) mod utils;

pub(crate) use builder::Builder;
pub(crate) use cfg::{BackwardCFG, EdgeKind, ForwardCFG, Method, MethodIndex};
pub(crate) use pfg::AndersonPFG;
use std::{fmt::Debug, hash::Hash};

pub trait InterproceduralCFG {
    type Node: Eq + Hash + Clone + Debug;
    type Method: Debug;

    /// Returns all start points of a given method. There may be
    /// more than one start point in case of a backward analysis.
    fn get_start_points_of(&self, method: &Self::Method) -> Vec<&Self::Node>;

    /// Returns all end points of a given method.
    fn get_end_points_of(&self, method: &Self::Method) -> Vec<&Self::Node>;

    /// Returns `true` if the given node is a call site.
    fn is_call(&self, node: &Self::Node) -> bool;

    /// Returns `true` if the given statement leads to a method return.
    /// For backward analyses may also be start statements.
    fn is_exit(&self, node: &Self::Node) -> bool;

    /// Returns true is this is a method's start statement. For backward
    /// analyses those may also be return or throws statements.
    fn is_start_point(&self, node: &Self::Node) -> bool;

    /// Returns true is this is a special method.
    fn is_special_method(&self, method: &Self::Method) -> bool;

    /// Returns the previous nodes of the node.
    fn get_preds_of(&self, node: &Self::Node) -> Vec<&Self::Node>;

    /// Returns the subsequent nodes of the node.
    fn get_succs_of(&self, node: &Self::Node) -> Vec<&Self::Node>;

    /// Returns all node to which a call could return. In the RHS paper,
    /// for every call there is just one return site. We, however, use as
    /// return site the successor nodes, of which there can be many in case
    /// of exceptional flow.
    fn get_return_sites_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Node>;

    /// Returns all callee methods for a given call.
    fn get_callees_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Method>;

    /// Returns the method containing the node.
    ///
    /// ## Note
    /// According to Rust's rule about lifetime elision:
    ///   1. Each elided lifetime in input position becomes a distinct lifetime parameter;
    ///   2. If there are multiple input lifetime positions, but one of them is `&self` or
    ///      `&mut self`, the lifetime of `self` is assigned to all elided output lifetimes.
    /// if we don't use `'a` here, the expanded signature of this function may looks like:
    /// ```
    /// fn get_method_of<'a, 'b>(&'a self, node: &'b Self::Node) -> &'a Self::Method;
    /// ```
    /// , and the compiler will complain about `A lifetime didn't match what was expected`.
    fn get_method_of<'a>(&'a self, node: &'a Self::Node) -> &Self::Method;

    /// Returns the nodes contained in the method.
    fn get_nodes_of(&self, method: &Self::Method) -> Vec<&Self::Node>;

    /// Returns all call sites within a given method.
    fn get_call_sites_within(&self, method: &Self::Method) -> Vec<&Self::Node>;

    /// Returns the set of all nodes that are neither call nor start nodes.
    fn get_non_call_and_start_nodes(&self) -> Vec<&Self::Node>;

    /// Returns the set of all nodes that are neither call nor end nodes.
    fn get_non_call_and_end_nodes(&self) -> Vec<&Self::Node>;
}
