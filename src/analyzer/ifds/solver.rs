use crate::control_flow::InterproceduralCFG;
use crate::ifds::{binary_domain::BinaryDomain, problem::IfdsProblem};
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

/// An edge function computes how a domain value changes when flowing from one
/// super-graph node to another. See Sagiv, Reps, Horwitz 1996.
///
/// ## Note
/// For now we only concern IFDS problems, hence we don't implement `EdgeFunction`
/// in a generic way and only consider binary domain.
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum EdgeFunction {
    /// This edge function maps every input to the stated bottom element. `AllBottom` is
    /// normally useful only in the context of an IFDS solver, which uses `AllBottom` to
    /// model reachability.
    AllBottom,
    /// This edge function sets everything to the top value.
    AllTop,
    /// This edge function passes every input directly without any changes.
    Identity,
}

impl EdgeFunction {
    /// Computes the value resulting from applying this function to source.
    fn compute_target(&self, src_val: BinaryDomain) -> BinaryDomain {
        match self {
            Self::AllBottom => BinaryDomain::bottom_element(),
            Self::AllTop => BinaryDomain::top_element(),
            Self::Identity => src_val,
        }
    }

    /// Composes this function with the second function, effectively returning a
    /// summary function that maps sources to targets exactly as if first this
    /// function had been applied and then the second function.
    fn compose_with(self, second_function: Self) -> Self {
        match self {
            Self::AllBottom => match second_function {
                Self::Identity => self,
                _ => second_function,
            },
            Self::AllTop => self,
            Self::Identity => second_function,
        }
    }

    /// Returns a function that represents that (element-wise) meet
    /// of this function with second function. Naturally, this is a
    /// symmetric operation.
    fn meet_with(self, second_function: Self) -> Self {
        match self {
            Self::AllBottom => self,
            Self::AllTop => second_function,
            Self::Identity => match second_function {
                Self::Identity | Self::AllTop => self,
                Self::AllBottom => second_function,
            },
        }
    }
}

/// A path edge always starts at a method's header and ends at some
/// statement within the same method. The edge summarizes the data
/// flows along all paths from the method's entry to this statement.
/// Path edges that end at one of the method's exit points are called
/// summary edges.
///
/// ## Note
/// Crucially, the IFDS solution algorithm computes such summaries only
/// once for each method.
struct PathEdge<Node, Fact> {
    src_fact: Fact,
    tgt: Node,
    tgt_fact: Fact,
}

/// Jump functions correspond to path edges in IFDS. They encode summaries
/// of flow functions, i.e., compositions of environment transformers. They
/// effectively store the composition of flow functions computed from the
/// method's start point to the current statement `n`. We write them as
/// <d1, n, d2>  with `d1 `being the transformer at the start point and `d2`
/// being the transformer at `n`. After the entire method was processed,
/// jump functions are turned into summary functions.
struct JumpFunctions<Node, Fact>
where
    Node: Eq + Hash + Copy,
    Fact: Eq + Hash + Copy,
{
    /// mapping from target node and value to a list of all source values and
    /// associated functions where the list is implemented as a mapping from
    /// the source value to the function. We exclude empty default functions.
    non_empty_reverse_lookup: HashMap<(Node, Fact), HashMap<Fact, EdgeFunction>>,
    /// mapping from source value and target node to a list of all target values
    /// and associated functions where the list is implemented as a mapping from
    /// the source value to the function. We exclude empty default functions.
    non_empty_forward_lookup: HashMap<(Fact, Node), HashMap<Fact, EdgeFunction>>,
    /// mapping from target node to a list of triples consisting of source value,
    /// target value and associated function, the triple is implemented by a mapping
    /// from the source value and target value to the function. We exclude empty
    /// default functions.
    non_empty_lookup_by_target_node: HashMap<Node, HashMap<(Fact, Fact), EdgeFunction>>,
}

impl<Node, Fact> JumpFunctions<Node, Fact>
where
    Node: Eq + Hash + Copy,
    Fact: Eq + Hash + Copy,
{
    pub fn new() -> Self {
        Self {
            non_empty_reverse_lookup: Default::default(),
            non_empty_forward_lookup: Default::default(),
            non_empty_lookup_by_target_node: Default::default(),
        }
    }

    /// Records a jump function. The source statement is implicit.
    pub fn add_function(
        &mut self,
        src_fact: Fact,
        tgt: Node,
        tgt_fact: Fact,
        edge_fn: EdgeFunction,
    ) {
        if edge_fn == EdgeFunction::AllTop {
            // Don't save the default function(`AllTop`).
            return;
        }

        self.non_empty_reverse_lookup
            .entry((tgt, tgt_fact))
            .or_default()
            .insert(src_fact, edge_fn);

        self.non_empty_forward_lookup
            .entry((src_fact, tgt))
            .or_default()
            .insert(tgt_fact, edge_fn);

        self.non_empty_lookup_by_target_node
            .entry(tgt)
            .or_default()
            .insert((src_fact, tgt_fact), edge_fn);
    }

    /// Returns, for a given target node and value all associated
    /// source values, and for each the associated edge function.
    /// The return value is a mapping from source value to function.
    pub fn reverse_lookup(
        &self,
        tgt: Node,
        tgt_fact: Fact,
    ) -> Option<&HashMap<Fact, EdgeFunction>> {
        self.non_empty_reverse_lookup.get(&(tgt, tgt_fact))
    }

    /// Returns, for a given source value and target statement all
    /// associated target values, and for each the associated edge function.
    /// The return value is a mapping from target value to function.
    pub fn forward_lookup(
        &self,
        src_fact: Fact,
        tgt: Node,
    ) -> Option<&HashMap<Fact, EdgeFunction>> {
        self.non_empty_forward_lookup.get(&(src_fact, tgt))
    }

    /// Returns for a given target statement all jump function records with this target.
    /// The return value is a set of records of the form (src_fact, tgt_fact, edge_fn).
    pub fn lookup_by_target(&self, tgt: Node) -> Option<&HashMap<(Fact, Fact), EdgeFunction>> {
        self.non_empty_lookup_by_target_node.get(&tgt)
    }
}

pub struct IfdsSolver<'graph, Icfg, Problem>
where
    Icfg: InterproceduralCFG,
    Problem: IfdsProblem,
    <Problem as IfdsProblem>::Fact: Copy,
{
    icfg: &'graph Icfg,
    dump_esg: bool,
    computed_intra_edges:
        HashMap<(Icfg::Node, Icfg::Node), HashMap<Problem::Fact, HashSet<Problem::Fact>>>,
    computed_inter_edges:
        HashMap<(Icfg::Node, Icfg::Node), HashMap<Problem::Fact, HashSet<Problem::Fact>>>,
    problem: Problem,
    zero_value: Problem::Fact,
    jump_functions: JumpFunctions<Icfg::Node, Problem::Fact>,
    /// The line 21 of original IFDS algorithm asks to evaluate the inverse of the flow function:
    /// find all call nodes <c, d4> from which an edge leads to the procedure start node <sp,
    /// d1>. This would require computing the inverse of the flow function, which can be
    /// difficult for many analyses. Moreover, even though <sp, d1> is reachable in G^#, many of
    /// its predecessors in E^# may not be, and enumerating them may be intractable. For
    /// example, for an alias set analysis, the number of predecessors for most nodes is 2^(|Var|
    /// −1), where |Var| is the number of variables in the calling procedure.
    ///
    /// In this implementation, here maintains a set `incoming` that records nodes that the
    /// analysis has observed to be reachable and predecessors of <sp, d1>. This solution is
    /// first proposed in Naeem, Lhotak and Rodriguez, 2010.
    incomings: HashMap<(Icfg::Node, Problem::Fact), HashMap<Icfg::Node, HashSet<Problem::Fact>>>,
    /// Stores summaries that were queried before they were computed
    end_summaries:
        HashMap<(Icfg::Node, Problem::Fact), HashMap<(Icfg::Node, Problem::Fact), EdgeFunction>>,
    values: HashMap<(Icfg::Node, Problem::Fact), BinaryDomain>,
}

impl<'graph, Icfg, Problem> IfdsSolver<'graph, Icfg, Problem>
where
    Icfg: InterproceduralCFG,
    Problem: IfdsProblem,
    <Problem as IfdsProblem>::Fact: Copy,
{
    pub fn new(problem: Problem, icfg: &'graph Icfg, dump_esg: bool) -> Self {
        let zero_value = Problem::zero_value();
        Self {
            icfg,
            dump_esg,
            computed_intra_edges: Default::default(),
            computed_inter_edges: Default::default(),
            problem,
            zero_value,
            jump_functions: JumpFunctions::new(),
            incomings: Default::default(),
            end_summaries: Default::default(),
            values: Default::default(),
        }
    }

    // TODO: Processes edges in concurrent threads to improve performance.
    pub fn solve(&mut self, entrance: &Icfg::Method) {
        let initial_seeds = self.problem.initial_seeds(self.icfg, entrance);

        for (sp, facts_at_sp) in &initial_seeds {
            for fact_at_sp in facts_at_sp {
                self.propagate(self.zero_value, *sp, *fact_at_sp, EdgeFunction::Identity);
            }
            self.jump_functions.add_function(
                self.zero_value,
                *sp,
                self.zero_value,
                EdgeFunction::Identity,
            )
        }

        for (sp, facts_at_sp) in &initial_seeds {
            for fact_at_sp in facts_at_sp {
                self.set_value(*sp, *fact_at_sp, BinaryDomain::bottom_element());
                self.propagate_value(*sp, *fact_at_sp, &initial_seeds);
            }
        }

        let non_call_or_start_nodes = self.icfg.get_non_call_and_start_nodes();
        let mut final_value = vec![];
        for node in non_call_or_start_nodes {
            let method = self.icfg.get_method_of(node);
            for sp in self.icfg.get_start_points_of(method) {
                let related_jump_fns = self.jump_functions.lookup_by_target(*node);
                if let Some(related_jump_fns) = related_jump_fns {
                    for ((src_fact, tgt_fact), jump_fn) in related_jump_fns {
                        let value = jump_fn.compute_target(self.get_value(*sp, *src_fact));
                        let meet_value = self.get_value(*node, *tgt_fact).meet(&value);
                        final_value.push((*node, *tgt_fact, meet_value));
                    }
                }
            }
        }

        for (node, fact, value) in final_value {
            self.set_value(node, fact, value);
        }
    }

    /// Propagates the flow further down the exploded super graph, merging any edge
    /// function that might already have been computed for targetVal at target.
    ///
    /// ## Parameters
    /// - `src_fact`: the source fact of the propagated summary edge
    /// - `tgt`: the target node
    /// - `tgt_fact`: the target fact at the target node
    /// - `edge_fn`: the new edge function computed from <sp, src_fact> to <tgt, tgt_fact>
    fn propagate(
        &mut self,
        src_fact: Problem::Fact,
        tgt: Icfg::Node,
        tgt_fact: Problem::Fact,
        edge_fn: EdgeFunction,
    ) {
        let jump_fn = self
            .jump_functions
            .reverse_lookup(tgt, tgt_fact)
            .and_then(|edge_fns| edge_fns.get(&src_fact))
            .map(|edge_fn| *edge_fn)
            .unwrap_or(EdgeFunction::AllTop);
        let prime_fn = jump_fn.meet_with(edge_fn);
        if prime_fn != jump_fn {
            self.jump_functions
                .add_function(src_fact, tgt, tgt_fact, prime_fn);

            let path_edge = PathEdge {
                src_fact,
                tgt,
                tgt_fact,
            };
            if self.icfg.is_call(&tgt) {
                self.process_call(path_edge);
            } else {
                if self.icfg.is_exit(&tgt) {
                    self.process_exit(path_edge);
                } else {
                    self.process_normal(path_edge);
                }
            }
        }
    }

    /// Processes a call site in the caller's context.For each possible callee,
    /// registers incoming call edges, also propagates call-to-return flows and
    /// summarized callee flows within the caller.
    fn process_call(&mut self, path_edge: PathEdge<Icfg::Node, Problem::Fact>) {
        let src_fact = path_edge.src_fact;
        let tgt = path_edge.tgt;
        let tgt_fact = path_edge.tgt_fact;

        let jump_fn = self
            .jump_functions
            .forward_lookup(src_fact, tgt)
            .and_then(|edge_fns| edge_fns.get(&tgt_fact))
            .map(|edge_fn| *edge_fn)
            .unwrap_or(EdgeFunction::AllTop);
        let return_sites = self.icfg.get_return_sites_of_call_at(&tgt);
        let callees = self.icfg.get_callees_of_call_at(&tgt);

        for callee in callees {
            let call_flow_function = self.problem.get_call_flow_function(&tgt, &callee);
            let facts_at_callee_sp = call_flow_function(&tgt_fact);
            let callee_sps = self.icfg.get_start_points_of(&callee);
            for callee_sp in callee_sps {
                let callee_sp = *callee_sp;
                if self.dump_esg {
                    self.save_edges(tgt, callee_sp, tgt_fact, &facts_at_callee_sp, true);
                }

                for fact_at_callee_sp in &facts_at_callee_sp {
                    let fact_at_callee_sp = *fact_at_callee_sp;
                    self.propagate(
                        fact_at_callee_sp,
                        callee_sp,
                        fact_at_callee_sp,
                        EdgeFunction::Identity,
                    );

                    // Registers the fact <callee_sp, fact_at_callee_sp> has an
                    // incoming edge from <tgt, tgt_fact>.
                    self.incomings
                        .entry((callee_sp, fact_at_callee_sp))
                        .or_default()
                        .entry(tgt)
                        .or_default()
                        .insert(tgt_fact);

                    let end_summary = self
                        .end_summaries
                        .get(&(callee_sp, fact_at_callee_sp))
                        .map(|end_summary| end_summary.clone());

                    // For each already-queried exit value <callee_ep, fact_at_callee_ep>
                    // reachable from <callee_sp, fact_at_callee_sp>, create new caller-side
                    // jump functions to the return sites because we have observed a potentially
                    // new incoming edge into <callee_sp, fact_at_callee_sp>
                    if let Some(end_summary) = end_summary {
                        for ((callee_ep, fact_at_callee_ep), summary_edge_fn) in end_summary {
                            for &return_site in &return_sites {
                                let return_flow_function = self.problem.get_return_flow_function(
                                    &tgt,
                                    callee,
                                    &callee_ep,
                                    return_site,
                                );
                                let facts_at_return_site = return_flow_function(&fact_at_callee_ep);
                                for fact_at_return_site in facts_at_return_site {
                                    // Updates the caller-side summary function
                                    let call_edge_fn = if tgt_fact == self.zero_value {
                                        EdgeFunction::AllBottom
                                    } else {
                                        EdgeFunction::Identity
                                    };
                                    let return_edge_fn = if fact_at_callee_ep == self.zero_value {
                                        EdgeFunction::AllBottom
                                    } else {
                                        EdgeFunction::Identity
                                    };
                                    let prime_fn = call_edge_fn
                                        .compose_with(summary_edge_fn)
                                        .compose_with(return_edge_fn);
                                    self.propagate(
                                        src_fact,
                                        *return_site,
                                        fact_at_return_site,
                                        jump_fn.compose_with(prime_fn),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        // Processes intra-procedural flows along call-to-return flow functions
        for return_site in return_sites {
            let call_to_return_flow_function = self
                .problem
                .get_call_to_return_flow_function(&tgt, &return_site);
            let facts_at_return_site = call_to_return_flow_function(&tgt_fact);
            if self.dump_esg {
                self.save_edges(tgt, *return_site, tgt_fact, &facts_at_return_site, true);
            }

            for fact_at_return_site in facts_at_return_site {
                let edge_fn = if tgt_fact == self.zero_value {
                    EdgeFunction::AllBottom
                } else {
                    EdgeFunction::Identity
                };
                self.propagate(src_fact, *return_site, fact_at_return_site, edge_fn)
            }
        }
    }

    /// Stores callee-side summaries. Also, at the side of the caller,
    /// propagates intra-procedural flows to return sites using those
    /// newly computed summaries.
    fn process_exit(&mut self, path_edge: PathEdge<Icfg::Node, Problem::Fact>) {
        let src_fact = path_edge.src_fact;
        let tgt = path_edge.tgt;
        let tgt_fact = path_edge.tgt_fact;

        let jump_fn = self
            .jump_functions
            .forward_lookup(src_fact, tgt)
            .and_then(|edge_fns| edge_fns.get(&tgt_fact))
            .map(|edge_fn| *edge_fn)
            .unwrap_or(EdgeFunction::AllTop);

        let callee = self.icfg.get_method_of(&tgt);
        let callee_sps = self.icfg.get_start_points_of(callee);
        //for each of the callee's start points, determine incoming calls
        for callee_sp in callee_sps {
            // Registers end summary
            let callee_sp = *callee_sp;
            self.end_summaries
                .entry((callee_sp, src_fact))
                .or_default()
                .insert((tgt, tgt_fact), jump_fn);

            let call_site_with_facts = self
                .incomings
                .get(&(callee_sp, src_fact))
                .map(|call_site_with_facts| call_site_with_facts.clone())
                .unwrap_or_default();

            for (call_site, facts_at_call_site) in call_site_with_facts {
                let return_sites = self.icfg.get_return_sites_of_call_at(&call_site);
                for return_site in return_sites {
                    let return_flow_function = self.problem.get_return_flow_function(
                        &call_site,
                        callee,
                        &tgt,
                        return_site,
                    );
                    let facts_at_return_site = return_flow_function(&tgt_fact);
                    if self.dump_esg {
                        self.save_edges(tgt, *return_site, tgt_fact, &facts_at_return_site, true);
                    }

                    for fact_at_call_site in &facts_at_call_site {
                        for fact_at_return_site in &facts_at_return_site {
                            let call_edge_fn = if fact_at_call_site == &self.zero_value {
                                EdgeFunction::AllBottom
                            } else {
                                EdgeFunction::Identity
                            };

                            let return_edge_fn = if tgt_fact == self.zero_value {
                                EdgeFunction::AllBottom
                            } else {
                                EdgeFunction::Identity
                            };

                            let prime_fn = call_edge_fn
                                .compose_with(jump_fn)
                                .compose_with(return_edge_fn);

                            // For each jump function coming into the call,
                            // propagates to return site using the composed
                            // function.
                            let fact_and_jump_fns = self
                                .jump_functions
                                .reverse_lookup(call_site, *fact_at_call_site)
                                .map(|fact_and_jump_fns| fact_and_jump_fns.clone())
                                .unwrap_or_default();
                            for (fact, jump_fn) in fact_and_jump_fns {
                                if jump_fn != EdgeFunction::AllTop {
                                    self.propagate(
                                        fact,
                                        *return_site,
                                        *fact_at_return_site,
                                        jump_fn.compose_with(prime_fn),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn process_normal(&mut self, path_edge: PathEdge<Icfg::Node, Problem::Fact>) {
        let src_fact = path_edge.src_fact;
        let tgt = path_edge.tgt;
        let tgt_fact = path_edge.tgt_fact;

        let jump_fn = self
            .jump_functions
            .forward_lookup(src_fact, tgt)
            .and_then(|edge_fns| edge_fns.get(&tgt_fact))
            .map(|edge_fn| *edge_fn)
            .unwrap_or(EdgeFunction::AllTop);

        for succ in self.icfg.get_succs_of(&tgt) {
            let normal_flow_function = self.problem.get_normal_flow_function(&tgt, &succ);
            let facts_of_succ = normal_flow_function(&tgt_fact);
            if self.dump_esg {
                self.save_edges(tgt, *succ, tgt_fact, &facts_of_succ, false);
            }
            let prime_fn = jump_fn.compose_with(if tgt_fact == self.zero_value {
                EdgeFunction::AllBottom
            } else {
                EdgeFunction::Identity
            });
            for fact_of_succ in facts_of_succ {
                self.propagate(src_fact, *succ, fact_of_succ, prime_fn);
            }
        }
    }

    fn save_edges(
        &mut self,
        src: Icfg::Node,
        tgt: Icfg::Node,
        src_fact: Problem::Fact,
        tgt_facts: &HashSet<Problem::Fact>,
        is_interprocedural: bool,
    ) {
        let computed_edges = if is_interprocedural {
            &mut self.computed_inter_edges
        } else {
            &mut self.computed_intra_edges
        };

        computed_edges
            .entry((src, tgt))
            .or_default()
            .entry(src_fact)
            .or_default()
            .extend(tgt_facts);
    }

    fn propagate_value(
        &mut self,
        node: Icfg::Node,
        fact: Problem::Fact,
        initial_seeds: &HashMap<Icfg::Node, HashSet<Problem::Fact>>,
    ) {
        let mut new_tasks = vec![];

        if self.icfg.is_start_point(&node) || initial_seeds.contains_key(&node) {
            let method = self.icfg.get_method_of(&node);
            for call_site in self.icfg.get_call_sites_within(&method) {
                let facts_and_jump_fns = self.jump_functions.forward_lookup(fact, *call_site);
                if let Some(facts_and_jump_fns) = facts_and_jump_fns {
                    for (fact_at_call_site, jump_fn) in facts_and_jump_fns {
                        let value = jump_fn.compute_target(self.get_value(node, fact));
                        new_tasks.push((*call_site, *fact_at_call_site, value));
                    }
                }
            }
        } else {
            if self.icfg.is_call(&node) {
                for callee in self.icfg.get_callees_of_call_at(&node) {
                    let call_flow_function = self.problem.get_call_flow_function(&node, callee);
                    for fact_at_callee_sp in call_flow_function(&fact) {
                        let call_edge_fn = if fact == self.zero_value {
                            EdgeFunction::AllBottom
                        } else {
                            EdgeFunction::Identity
                        };

                        for callee_sp in self.icfg.get_start_points_of(callee) {
                            let value = call_edge_fn.compute_target(self.get_value(node, fact));
                            new_tasks.push((*callee_sp, fact_at_callee_sp, value))
                        }
                    }
                }
            }
        }

        for (node, fact, value) in new_tasks {
            self.propagate_new_value(node, fact, value, initial_seeds);
        }
    }

    fn propagate_new_value(
        &mut self,
        node: Icfg::Node,
        fact: Problem::Fact,
        value: BinaryDomain,
        initial_seeds: &HashMap<Icfg::Node, HashSet<Problem::Fact>>,
    ) {
        let old_value = self.get_value(node, fact);
        let meet_value = old_value.meet(&value);
        if meet_value != old_value {
            self.set_value(node, fact, meet_value);
            self.propagate_value(node, fact, initial_seeds);
        }
    }

    fn set_value(&mut self, node: Icfg::Node, fact: Problem::Fact, value: BinaryDomain) {
        if value == BinaryDomain::top_element() {
            self.values.remove(&(node, fact));
        } else {
            self.values.insert((node, fact), value);
        }
    }

    fn get_value(&self, node: Icfg::Node, fact: Problem::Fact) -> BinaryDomain {
        self.values
            .get(&(node, fact))
            .map(|value| *value)
            .unwrap_or(BinaryDomain::top_element())
    }
}
