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

use crate::control_flow::{EdgeKind, EdgeWeight, InterproceduralCFG, Method, Node};
use either::*;
use log::*;
use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
    Direction,
};
use rustc_hir::{def::DefKind, def_id::DefId, definitions::DefPathData};
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, BindingForm, Body, ClearCrossCrate, ImplicitSelfKind, Local,
        LocalInfo, START_BLOCK,
    },
    ty::{subst::InternalSubsts, DefIdTree, TyCtxt, TyKind, Visibility},
};
use std::{
    collections::HashMap,
    fmt, fs,
    io::{self, Write},
    ops::{Deref, Index},
    path::Path,
};

#[derive(Debug)]
pub struct MethodInfo {
    pub mutable: bool,
    pub visible: bool,
    pub name: String,
}

pub struct ForwardCFG<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub contract_methods: HashMap<DefId, MethodInfo>,
    pub external_methods: HashMap<DefId, MethodInfo>,

    pub(in crate::control_flow) method_start_point: HashMap<Method<'tcx>, Node<'tcx>>,
    pub(in crate::control_flow) method_end_points: HashMap<Method<'tcx>, Vec<Node<'tcx>>>,
    pub(in crate::control_flow) node_to_index: HashMap<Node<'tcx>, NodeIndex>,
    pub(in crate::control_flow) method_basic_blocks:
        HashMap<DefId, HashMap<BasicBlock, BasicBlockData<'tcx>>>,
    inner_graph: DiGraph<Node<'tcx>, EdgeWeight<'tcx>>,
}

impl<'tcx> ForwardCFG<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let (contract_methods, external_methods) = collect_method_infos(tcx);
        Self {
            tcx,
            contract_methods,
            external_methods,
            method_start_point: Default::default(),
            method_end_points: Default::default(),
            node_to_index: Default::default(),
            inner_graph: Default::default(),
            method_basic_blocks: Default::default(),
        }
    }

    #[inline]
    pub fn add_node(&mut self, node: Node<'tcx>) -> NodeIndex {
        self.inner_graph.add_node(node)
    }

    #[inline]
    pub fn add_edge(&mut self, from: NodeIndex, to: NodeIndex, edge: EdgeWeight<'tcx>) {
        self.inner_graph.add_edge(from, to, edge);
    }

    /// Converts the call graph into DOT-described document
    /// and saves in a local file.
    pub fn dump(&self, path: &Path, entry_points: &Vec<Method<'tcx>>) -> io::Result<()> {
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
        for (i, node) in self.inner_graph.raw_nodes().iter().enumerate() {
            let node = &node.weight;
            let belongs_to = node.belongs_to;
            node_groups
                .entry(belongs_to)
                .or_insert(vec![])
                .push((i, node));
        }

        let mut edge_groups = HashMap::new();
        let mut cross_edges = vec![];
        for edge in self.inner_graph.raw_edges() {
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

        /*<tr><td colspan=\"3\">The foo, the bar and the baz</td></tr><tr><td colspan=\"3\">The foo, the bar and the baz</td></tr>*/
        for (i, (method, nodes)) in node_groups.iter().enumerate() {
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
                use std::fmt::Write;
                let BasicBlockData {
                    ref statements,
                    ref terminator,
                    ..
                } = self.method_basic_blocks[&node.belongs_to.def_id][&node.basic_block];
                write!(dot_file, "        {} [label=\"", i);
                let mut escaper = Escaper::new(&mut dot_file, EscapeMode::Dot);
                for statement in statements {
                    write!(escaper, "{:?};\n", statement);
                }
                if let Some(terminator) = terminator {
                    write!(escaper, "{:?};\n", terminator.kind);
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
        let entry_point_indices = entry_points.iter().fold(vec![], |mut acc, entry_point| {
            acc.push(self.node_to_index[&self.method_start_point[&entry_point]]);
            acc
        });
        for entry_point_index in entry_point_indices {
            writeln!(dot_file, "    start -> {}", entry_point_index.index());
        }
        writeln!(dot_file, "}}")
    }
}

fn collect_method_infos<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> (HashMap<DefId, MethodInfo>, HashMap<DefId, MethodInfo>) {
    let mut contract_methods = HashMap::new();
    let mut external_methods = HashMap::new();
    for local_def_id in tcx.body_owners() {
        let def_id = local_def_id.to_def_id();

        match get_method_info(tcx, def_id) {
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
) -> Option<Either<MethodInfo, MethodInfo>> {
    const STORAGE_DEF_PATH: [&str; 3] = ["Storage", "__liquid_storage", "__liquid_private"];
    const INTERFACE_DEF_PATH: [&str; 3] = ["Interface", "__liquid_interface", "__liquid_private"];

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

        if def_path_suffix == STORAGE_DEF_PATH {
            let visible = tcx.visibility(def_id) == Visibility::Public;
            let mutable = is_mutable(body);
            return Some(Left(MethodInfo {
                mutable,
                visible,
                name,
            }));
        }

        if def_path_suffix == INTERFACE_DEF_PATH {
            if name != "at" {
                let mutable = is_mutable(body);
                return Some(Right(MethodInfo {
                    mutable,
                    visible: true,
                    name,
                }));
            }
        }
    }
    None
}

impl<'tcx> InterproceduralCFG for ForwardCFG<'tcx> {
    type Node = Node<'tcx>;
    type Method = Method<'tcx>;

    fn get_start_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        vec![self.method_start_point.index(method)]
    }

    fn get_end_points_of(&self, method: &Self::Method) -> Vec<&Self::Node> {
        self.method_end_points[method].iter().collect()
    }

    fn is_call(&self, node: &Self::Node) -> bool {
        let node_index = self.node_to_index[node];
        self.inner_graph
            .edges_directed(node_index, Direction::Outgoing)
            .all(|edge| edge.weight().kind == EdgeKind::Call)
    }

    fn is_exit(&self, node: &Self::Node) -> bool {
        let node_index = self.node_to_index[node];
        self.inner_graph
            .edges_directed(node_index, Direction::Outgoing)
            .all(|edge| edge.weight().kind == EdgeKind::Return)
    }

    fn is_start_point(&self, node: &Self::Node) -> bool {
        node.basic_block == START_BLOCK
    }

    fn get_succs_of(&self, node: &Self::Node) -> Vec<&Self::Node> {
        let node_index = self.node_to_index[node];
        self.inner_graph
            .neighbors_directed(node_index, Direction::Outgoing)
            .map(|neighbor| self.inner_graph.node_weight(neighbor).unwrap())
            .collect()
    }

    fn get_return_sites_of_call_at(&self, node: &Self::Node) -> Vec<&Self::Node> {
        debug_assert!(self.is_call(node));

        let node_index = self.node_to_index[node];
        self.inner_graph
            .edges(node_index)
            .filter_map(|edge| {
                if edge.weight().kind == EdgeKind::CallToReturn {
                    let node = self.inner_graph.node_weight(edge.target()).unwrap();
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
        self.inner_graph
            .edges(node_index)
            .filter_map(|edge| {
                if edge.weight().kind == EdgeKind::Call {
                    let node = self.inner_graph.node_weight(edge.target()).unwrap();
                    Some(&node.belongs_to)
                } else {
                    None
                }
            })
            .collect()
    }

    fn get_method_of<'a>(&self, node: &'a Self::Node) -> &'a Self::Method {
        &node.belongs_to
    }

    fn get_call_sites_within(&self, method: &Self::Method) -> Vec<&Self::Node> {
        let mut call_sites = vec![];
        for node in self
            .inner_graph
            .raw_nodes()
            .iter()
            .filter(|node| &node.weight.belongs_to == method)
        {
            if self.is_call(&node.weight) {
                call_sites.push(&node.weight);
            }
        }
        call_sites
    }

    fn get_non_call_and_start_nodes(&self) -> Vec<&Self::Node> {
        self.inner_graph
            .raw_nodes()
            .iter()
            .filter_map(|node| {
                let node = &node.weight;
                if self.is_call(node) || self.is_start_point(node) {
                    None
                } else {
                    Some(node)
                }
            })
            .collect()
    }
}
