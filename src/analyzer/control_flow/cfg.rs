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

use crate::control_flow::{utils, InterproceduralCFG};
use log::*;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
    Direction,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::{subst::SubstsRef, Ty};
use rustc_middle::{
    mir::{BasicBlockData, TerminatorKind, START_BLOCK},
    ty::{subst::InternalSubsts, TyCtxt},
};
use std::{
    collections::HashMap,
    fmt, fs,
    io::{self, Write},
    path::Path,
};

pub type MethodIndex = usize;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Method<'tcx> {
    pub def_id: DefId,
    pub substs: SubstsRef<'tcx>,
    pub self_ty: Option<Ty<'tcx>>,
    pub used_for_clone: bool,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum NodeKind {
    Normal,
    Call,
    Start,
    End,
    Fake(utils::SpecialCause),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Node {
    pub basic_block: Option<BasicBlock>,
    pub belongs_to: MethodIndex,
    pub kind: NodeKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    Normal,
    Call,
    Return,
    CallToReturn,
}

#[derive(Copy, Clone, Debug)]
pub struct Edge<'tcx> {
    pub container: Option<Method<'tcx>>,
    pub kind: EdgeKind,
    pub is_certain: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct CallSite {
    pub caller: MethodIndex,
    pub bb_id: usize,
}

pub struct ForwardCFG<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub(in crate::control_flow) start_point: HashMap<MethodIndex, NodeIndex>,
    pub(in crate::control_flow) end_points: HashMap<MethodIndex, Vec<NodeIndex>>,
    pub(in crate::control_flow) methods: Vec<Method<'tcx>>,
    pub(in crate::control_flow) graph: DiGraph<Node, Edge<'tcx>>,
    pub(in crate::control_flow) node_to_index: HashMap<Node, NodeIndex>,
}

impl<'tcx> ForwardCFG<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            methods: Default::default(),
            start_point: Default::default(),
            end_points: Default::default(),
            node_to_index: Default::default(),
            graph: Default::default(),
        }
    }

    #[inline]
    pub fn add_node(&mut self, node: Node) -> NodeIndex {
        self.graph.add_node(node)
    }

    #[inline]
    pub fn add_edge(&mut self, from: NodeIndex, to: NodeIndex, edge: Edge<'tcx>) {
        self.graph.add_edge(from, to, edge);
    }

    #[inline]
    pub fn get_method_by_def_id(&self, def_id: DefId) -> &Method<'tcx> {
        self.methods
            .iter()
            .find(|method| method.def_id == def_id)
            .unwrap()
    }

    #[inline]
    pub fn get_method_index(&self, method: &Method<'tcx>) -> MethodIndex {
        self.methods.iter().position(|m| m == method).unwrap()
    }

    #[inline]
    pub fn get_method_by_index(&self, index: MethodIndex) -> &Method<'tcx> {
        self.methods.get(index).unwrap()
    }

    /// Converts the call graph into DOT-described document
    /// and saves in a local file.
    pub fn dump(&self, path: &Path, ep_count: usize) -> io::Result<()> {
        #[derive(PartialEq, Eq)]
        enum EscapeMode {
            Dot,
            Html,
        }
        struct Escaper<'a, W>
        where
            W: io::Write,
        {
            writer: &'a mut W,
            mode: EscapeMode,
        }

        impl<'a, W> Escaper<'a, W>
        where
            W: io::Write,
        {
            fn new(writer: &'a mut W, mode: EscapeMode) -> Self {
                Escaper { writer, mode }
            }
        }

        impl<'a, W> fmt::Write for Escaper<'a, W>
        where
            W: io::Write,
        {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                for c in s.chars() {
                    self.write_char(c)?
                }
                Ok(())
            }

            fn write_char(&mut self, c: char) -> fmt::Result {
                let result = if self.mode == EscapeMode::Dot {
                    match c {
                        '"' => write!(self.writer, "\\\""),
                        '\\' => write!(self.writer, "\\\\"),
                        _ => write!(self.writer, "{}", c),
                    }
                } else {
                    match c {
                        '<' => write!(self.writer, "&lt;"),
                        '>' => write!(self.writer, "&gt;"),
                        '&' => write!(self.writer, "&amp;"),
                        _ => write!(self.writer, "{}", c),
                    }
                };

                if result.is_err() {
                    Err(fmt::Error)
                } else {
                    Ok(())
                }
            }
        }

        let mut dot_file = fs::File::create(path)?;
        writeln!(dot_file, "strict digraph {{")?;
        writeln!(dot_file, "    node [fontname=monospace shape=box]")?;
        writeln!(dot_file, "    edge [samehead=h1, sametail=t1]")?;
        writeln!(dot_file, "    rankdir=TB");

        let mut node_groups = HashMap::new();
        for (i, node) in self.graph.raw_nodes().iter().enumerate() {
            let node = &node.weight;
            let belongs_to = node.belongs_to;
            node_groups
                .entry(belongs_to)
                .or_insert(vec![])
                .push((i, node));
        }

        let mut edge_groups = HashMap::new();
        let mut cross_edges = vec![];
        for edge in self.graph.raw_edges() {
            let src_idx = edge.source().index();
            let tgt_idx = edge.target().index();
            let weight = edge.weight;
            let edge_info = (src_idx, tgt_idx, weight);
            if let Some(container) = edge.weight.container {
                edge_groups
                    .entry(container)
                    .or_insert(vec![])
                    .push(edge_info);
            } else {
                cross_edges.push(edge_info);
            }
        }

        for (i, (method_index, nodes)) in node_groups.iter().enumerate() {
            let method = self.get_method_by_index(*method_index);
            writeln!(dot_file, "    subgraph cluster_{} {{", i);
            writeln!(dot_file, "        label=<<table border='1' cellborder='1'>");
            {
                write!(dot_file, "<tr><td colspan=\"2\">");
                use std::fmt::Write;
                let mut escaper = Escaper::new(&mut dot_file, EscapeMode::Html);
                write!(escaper, "{:?}", method.def_id);
                write!(dot_file, "</td></tr>");
            }
            let substs = &method.substs;
            let self_ty = &method.self_ty;
            if !substs.is_empty() || self_ty.is_some() {
                use std::fmt::Write;

                if let Some(self_ty) = self_ty {
                    write!(dot_file, "<tr><td>Self</td><td>");
                    let mut escaper = Escaper::new(&mut dot_file, EscapeMode::Html);
                    write!(escaper, "{}", self_ty);
                    write!(dot_file, "</td></tr>");
                }

                InternalSubsts::for_item(self.tcx, method.def_id, |param_def, _| {
                    let actual_arg = substs.get(param_def.index as usize);
                    debug_assert!(actual_arg.is_some());
                    let actual_arg = actual_arg.unwrap();
                    write!(dot_file, "<tr><td>{}</td><td>", param_def.name);
                    let mut escaper = Escaper::new(&mut dot_file, EscapeMode::Html);
                    write!(escaper, "{}", actual_arg);
                    write!(dot_file, "</td></tr>");
                    self.tcx.mk_param_from_def(param_def)
                });
            }
            writeln!(dot_file, "</table>>")?;

            for (i, node) in nodes {
                let method = self.get_method_by_index(node.belongs_to);
                use std::fmt::Write;
                write!(dot_file, "        {} [label=\"", i);

                let mut escaper = Escaper::new(&mut dot_file, EscapeMode::Dot);

                match node.kind {
                    NodeKind::Call => {
                        let basic_block = node.basic_block.unwrap();
                        write!(escaper, "bb{}(call-counterpart):\n", basic_block.as_usize());
                        let terminator = self.tcx.optimized_mir(method.def_id).basic_blocks()
                            [basic_block]
                            .terminator
                            .as_ref();
                        // For call nodes, don't print the statements but only print `Call` terminator.
                        if let Some(terminator) = terminator {
                            write!(escaper, "{:?};\n", terminator.kind);
                        }
                    }
                    NodeKind::Normal => {
                        let basic_block = node.basic_block.unwrap();
                        write!(escaper, "bb{}:\n", basic_block.as_usize());
                        let BasicBlockData {
                            ref statements,
                            ref terminator,
                            ..
                        } = self.tcx.optimized_mir(method.def_id).basic_blocks()[basic_block];

                        for statement in statements {
                            write!(escaper, "{:?};\n", statement);
                        }
                        if let Some(terminator) = terminator {
                            if !matches!(terminator.kind, TerminatorKind::Call { .. }) {
                                write!(escaper, "{:?};\n", terminator.kind);
                            }
                        }
                    }
                    NodeKind::Start => {
                        write!(escaper, "start node");
                    }
                    NodeKind::End => {
                        write!(escaper, "end node");
                    }
                    NodeKind::Fake(cause) => {
                        write!(escaper, "{:?}", cause);
                    }
                }
                writeln!(dot_file, "\"]");
            }

            if let Some(edges) = &edge_groups.get(method) {
                for (src_idx, tgt_idx, weight) in edges.iter() {
                    let attr = if weight.kind == EdgeKind::CallToReturn {
                        " [color=purple,label=\"CALL_TO_RETURN\",style=bold]"
                    } else {
                        ""
                    };
                    writeln!(dot_file, "        {} -> {}{}", src_idx, tgt_idx, attr);
                }
            }

            writeln!(dot_file, "    }}");
        }

        for (srg_idx, tgt_idx, weight) in cross_edges {
            write!(dot_file, "    {} -> {} [style=bold,", srg_idx, tgt_idx);
            let kind = weight.kind;
            match kind {
                EdgeKind::Call => {
                    write!(dot_file, "color=blue,label=\"CALL\"");
                }
                EdgeKind::Return => {
                    write!(dot_file, "color=green,label=\"RETURN\"");
                }
                _ => unreachable!(),
            }
            if !weight.is_certain {
                write!(dot_file, ",style=dashed");
            }
            writeln!(dot_file, "]");
        }

        writeln!(dot_file, "    start [shape=Mdiamond]");
        let ep_indices = (0..ep_count).fold(vec![], |mut acc, ep_index| {
            acc.push(self.start_point[&ep_index]);
            acc
        });
        for ep_index in ep_indices {
            writeln!(dot_file, "    start -> {}", ep_index.index());
        }
        writeln!(dot_file, "}}")
    }
}
impl<'tcx> InterproceduralCFG for ForwardCFG<'tcx> {
    type Node = Node;
    type Method = Method<'tcx>;

    fn get_start_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        debug!("get_start_points_of {:?}", method);
        let method_index = self.get_method_index(method);
        let start_point = self.start_point[&method_index];
        vec![self.graph.node_weight(start_point).unwrap()]
    }

    fn get_end_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        let method_index = self.get_method_index(method);
        self.end_points[&method_index]
            .iter()
            .map(|node_index| self.graph.node_weight(*node_index).unwrap())
            .collect()
    }

    fn is_call(&self, node: &Self::Node) -> bool {
        node.kind == NodeKind::Call
    }

    fn is_exit(&self, node: &Self::Node) -> bool {
        node.kind == NodeKind::End
    }

    fn is_start_point(&self, node: &Self::Node) -> bool {
        node.kind == NodeKind::Start
    }

    fn is_special_method(&self, method: &Self::Method) -> bool {
        utils::is_special_method(self.tcx, method.def_id).is_some()
    }

    fn get_preds_of(&self, node: &Self::Node) -> Vec<&Self::Node> {
        let node_index = self.node_to_index[node];
        self.graph
            .edges_directed(node_index, Direction::Incoming)
            .filter(|edge| !matches!(edge.weight().kind, EdgeKind::Call | EdgeKind::Return))
            .map(|edge| self.graph.node_weight(edge.source()).unwrap())
            .collect()
    }

    fn get_succs_of(&self, node: &Self::Node) -> Vec<&Self::Node> {
        let node_index = self.node_to_index[node];
        self.graph
            .edges_directed(node_index, Direction::Outgoing)
            .filter(|edge| !matches!(edge.weight().kind, EdgeKind::Call | EdgeKind::Return))
            .map(|edge| self.graph.node_weight(edge.target()).unwrap())
            .collect()
    }

    fn get_return_sites_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Node> {
        debug_assert!(self.is_call(node));

        let node_index = self.node_to_index[node];
        self.graph
            .edges(node_index)
            .filter_map(|edge| {
                if edge.weight().kind == EdgeKind::CallToReturn {
                    let node = self.graph.node_weight(edge.target()).unwrap();
                    Some(node)
                } else {
                    None
                }
            })
            .collect()
    }

    fn get_callees_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Method> {
        debug_assert!(self.is_call(node));

        let node_index = self.node_to_index[node];
        self.graph
            .edges(node_index)
            .filter_map(|edge| {
                if edge.weight().kind == EdgeKind::Call {
                    let node = self.graph.node_weight(edge.target()).unwrap();
                    Some(&node.belongs_to)
                } else {
                    None
                }
            })
            .map(|method_index| self.get_method_by_index(*method_index))
            .collect()
    }

    fn get_method_of<'a>(&'a self, node: &'a Self::Node) -> &Self::Method {
        self.get_method_by_index(node.belongs_to)
    }

    fn get_nodes_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        let method_index = self.methods.iter().position(|m| m == method).unwrap();
        self.graph
            .raw_nodes()
            .iter()
            .filter_map(|node| {
                let node = &node.weight;
                if node.belongs_to == method_index {
                    Some(node)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    }

    fn get_call_sites_within(&self, method: &Self::Method) -> Vec<&Self::Node> {
        let mut call_sites = vec![];
        for node in self
            .graph
            .raw_nodes()
            .iter()
            .filter(|node| self.get_method_by_index(node.weight.belongs_to) == method)
        {
            if self.is_call(&node.weight) {
                call_sites.push(&node.weight);
            }
        }
        call_sites
    }

    fn get_non_call_and_start_nodes(&self) -> Vec<&Self::Node> {
        self.graph
            .raw_nodes()
            .iter()
            .filter_map(|node| {
                let node = &node.weight;
                if self.is_call(node)
                    || self.is_start_point(node)
                    || matches!(node.kind, NodeKind::Fake(..))
                {
                    None
                } else {
                    Some(node)
                }
            })
            .collect()
    }

    fn get_non_call_and_end_nodes(&self) -> Vec<&Self::Node> {
        self.graph
            .raw_nodes()
            .iter()
            .filter_map(|node| {
                let node = &node.weight;
                if self.is_call(node)
                    || self.is_exit(node)
                    || matches!(node.kind, NodeKind::Fake(..))
                {
                    None
                } else {
                    Some(node)
                }
            })
            .collect()
    }
}

pub struct BackwardCFG<'graph, 'tcx> {
    pub fwd_cfg: &'graph ForwardCFG<'tcx>,
}

impl<'graph, 'tcx> BackwardCFG<'graph, 'tcx> {
    pub fn new(fwd_cfg: &'graph ForwardCFG<'tcx>) -> Self {
        Self { fwd_cfg }
    }

    #[inline]
    pub fn get_method_by_index(&self, index: MethodIndex) -> &Method<'tcx> {
        self.fwd_cfg.methods.get(index).unwrap()
    }
}

impl<'graph, 'tcx> InterproceduralCFG for BackwardCFG<'graph, 'tcx> {
    type Node = <ForwardCFG<'tcx> as InterproceduralCFG>::Node;
    type Method = <ForwardCFG<'tcx> as InterproceduralCFG>::Method;

    fn get_start_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        self.fwd_cfg.get_end_points_of(method)
    }

    fn get_end_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        self.fwd_cfg.get_start_points_of(method)
    }

    fn is_call(&self, node: &Self::Node) -> bool {
        self.fwd_cfg.is_call(node)
    }

    fn is_exit(&self, node: &Self::Node) -> bool {
        self.fwd_cfg.is_start_point(node)
    }

    fn is_start_point(&self, node: &Self::Node) -> bool {
        self.fwd_cfg.is_exit(node)
    }

    fn is_special_method(&self, method: &Self::Method) -> bool {
        self.fwd_cfg.is_special_method(method)
    }

    fn get_preds_of(&self, node: &Self::Node) -> Vec<&Self::Node> {
        self.fwd_cfg.get_succs_of(node)
    }

    fn get_succs_of(&self, node: &Self::Node) -> Vec<&Self::Node> {
        self.fwd_cfg.get_preds_of(node)
    }

    fn get_return_sites_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Node> {
        debug_assert!(self.is_call(node));
        self.fwd_cfg.get_preds_of(node)
    }

    fn get_callees_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Method> {
        self.fwd_cfg.get_callees_of_call_at(node)
    }

    fn get_method_of<'a>(&'a self, node: &'a Self::Node) -> &Self::Method {
        self.fwd_cfg.get_method_of(node)
    }

    fn get_nodes_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        self.fwd_cfg.get_nodes_of(method)
    }

    fn get_call_sites_within(&self, method: &Self::Method) -> Vec<&Self::Node> {
        self.fwd_cfg.get_call_sites_within(method)
    }

    fn get_non_call_and_start_nodes(&self) -> Vec<&Self::Node> {
        self.fwd_cfg.get_non_call_and_end_nodes()
    }

    fn get_non_call_and_end_nodes(&self) -> Vec<&Self::Node> {
        self.fwd_cfg.get_non_call_and_start_nodes()
    }
}
