use crate::{
    control_flow::{AndersonPFG, BackwardCFG, InterproceduralCFG, Method, MethodIndex},
    ifds::problem::{FlowFunction, IfdsProblem},
    known_names::KnownNames,
};
use either::*;
#[allow(unused_imports)]
use log::*;
use rustc_middle::{
    mir::{
        interpret::{AllocRange, ConstValue, GlobalAlloc, Scalar},
        BorrowKind, Constant, ConstantKind, Local, Mutability, Operand, Place, PlaceElem, Rvalue,
        StatementKind, TerminatorKind, RETURN_PLACE,
    },
    ty::{ConstKind, ParamEnv, ScalarInt, Ty, TyCtxt, TyKind},
};
use rustc_mir::dataflow::{impls::MaybeBorrowedLocals, Analysis};
use rustc_span::def_id::DefId;
use rustc_target::abi::Size;
use std::{
    collections::{HashMap, HashSet},
    convert::TryFrom,
    iter::FromIterator,
};

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct AccessPath {
    pub base: Local,
    pub fields: Vec<usize>,
}

impl<'tcx> TryFrom<&'tcx Place<'tcx>> for AccessPath {
    type Error = ();
    fn try_from(value: &'tcx Place<'tcx>) -> Result<Self, Self::Error> {
        let base = value.local;
        let mut fields = vec![];
        for place_elem in value.projection {
            match place_elem {
                PlaceElem::Field(field, _) => fields.push(field.as_usize()),
                PlaceElem::Downcast(_, variant_idx) => fields.push(variant_idx.as_usize()),
                _ => return Err(()),
            }
        }
        Ok(AccessPath { base, fields })
    }
}

pub struct ConflictFields<'tcx, 'graph> {
    tcx: TyCtxt<'tcx>,
    icfg: &'graph BackwardCFG<'graph, 'tcx>,
    pfg: AndersonPFG<'graph, 'tcx>,
    entry_point: MethodIndex,
    var_defs: HashMap<DefId, HashMap<Local, Vec<AccessPath>>>,
    maybe_mut_borrowed: HashMap<DefId, HashSet<Local>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum EnvKind {
    Caller,
    Origin,
    Now,
    BlockNumber,
    Address,
}

impl From<KnownNames> for EnvKind {
    fn from(fn_name: KnownNames) -> Self {
        match fn_name {
            KnownNames::LiquidEnvGetCaller => EnvKind::Caller,
            KnownNames::LiquidEnvGetOrigin => EnvKind::Origin,
            KnownNames::LiquidEnvNow => EnvKind::Now,
            KnownNames::LiquidEnvGetAddress => EnvKind::Address,
            KnownNames::LiquidEnvGetBlockNumber => EnvKind::BlockNumber,
            _ => unreachable!(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Key {
    All,
    Len,
    Env(EnvKind),
    Var(DefId, AccessPath),
    Const(Vec<u8>),
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
                var_defs: Default::default(),
                maybe_mut_borrowed: Default::default(),
            }
        } else {
            unreachable!("`Storage` should be a struct type")
        }
    }

    fn insert_var_defs(&mut self, method: &Method<'tcx>) {
        let def_id = method.def_id;
        if self.var_defs.contains_key(&def_id) {
            return;
        }
        self.var_defs.entry(def_id).or_default();
        let body = self.tcx.optimized_mir(def_id);
        let basic_blocks = body.basic_blocks();

        let mut record_def =
            |l_local: Local, r_local: Local, projection: &'tcx [PlaceElem<'tcx>]| {
                let mut fields = vec![];
                for place_elem in projection {
                    match place_elem {
                        PlaceElem::Field(field, _) => fields.push(field.as_usize()),
                        PlaceElem::Downcast(_, variant_idx) => fields.push(variant_idx.as_usize()),
                        _ => return,
                    }
                }
                self.var_defs
                    .get_mut(&def_id)
                    .unwrap()
                    .entry(l_local)
                    .or_default()
                    .push(AccessPath {
                        base: r_local,
                        fields,
                    });
            };

        for bb in basic_blocks.indices() {
            let stmts = &basic_blocks[bb].statements;
            for stmt in stmts {
                match &stmt.kind {
                    StatementKind::Assign(box (l_place, r_value)) => {
                        if l_place.projection.len() == 0 {
                            match r_value {
                                Rvalue::Use(r_operand) => match r_operand {
                                    Operand::Move(r_place) | Operand::Copy(r_place) => {
                                        record_def(
                                            l_place.local,
                                            r_place.local,
                                            r_place.projection,
                                        );
                                    }
                                    _ => (),
                                },
                                Rvalue::Ref(_, borrow_kind, r_place) => {
                                    if borrow_kind == &BorrowKind::Shared {
                                        let last_proj = r_place.as_ref().last_projection();
                                        if let Some((_, last_proj)) = last_proj {
                                            if last_proj == PlaceElem::Deref {
                                                record_def(
                                                    l_place.local,
                                                    r_place.local,
                                                    &r_place.projection[1..],
                                                );
                                            } else {
                                                record_def(
                                                    l_place.local,
                                                    r_place.local,
                                                    r_place.projection,
                                                );
                                            }
                                        } else {
                                            record_def(l_place.local, r_place.local, &[]);
                                        }
                                    }
                                }
                                _ => (),
                            }
                        }
                    }
                    _ => (),
                }
            }
        }

        let param_env = ParamEnv::reveal_all();
        let mut results = MaybeBorrowedLocals::mut_borrows_only(self.tcx, body, param_env)
            .unsound_ignore_borrow_on_drop()
            .into_engine(self.tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let mut maybe_mut_borrowed_in_method = HashSet::new();
        for bb in body.basic_blocks().indices() {
            results.seek_before_primary_effect(body.terminator_loc(bb));
            let state = results.get();
            for local in state.iter() {
                maybe_mut_borrowed_in_method.insert(local);
            }
        }

        self.maybe_mut_borrowed
            .insert(def_id, maybe_mut_borrowed_in_method);
    }

    fn reify(&self, access_path: AccessPath, def_id: DefId) -> Vec<AccessPath> {
        if let Some(method_defs) = self.var_defs.get(&def_id) {
            if let Some(defs) = method_defs.get(&access_path.base) {
                let mut results = vec![];
                for def in defs {
                    if !def.fields.is_empty() {
                        let mut composed_fields = def.fields.clone();
                        composed_fields.extend(&access_path.fields);
                        results.extend(self.reify(
                            AccessPath {
                                base: def.base,
                                fields: composed_fields,
                            },
                            def_id,
                        ));
                    }
                }

                if !results.is_empty() {
                    return results;
                }
            }
        }
        vec![access_path]
    }

    fn process_assignment(
        &self,
        dst: &Place<'tcx>,
        src: Option<&Place<'tcx>>,
        dst_method_id: DefId,
        src_method_id: DefId,
    ) -> FlowFunction<'tcx, <Self as IfdsProblem<'tcx>>::Fact> {
        let dst = AccessPath::try_from(dst);
        if dst.is_err() {
            return Self::identity();
        }
        let dst = dst.unwrap();

        if src.is_none() {
            if dst.fields.is_empty() {
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if let Key::Var(_, access_path) = key {
                            if dst.base == access_path.base {
                                let key = Key::All;
                                results.insert(ConflictField::Field {
                                    container: *container,
                                    key,
                                    read_only: *read_only,
                                });
                            } else {
                                results.insert(fact.clone());
                            }
                        } else {
                            results.insert(fact.clone());
                        }
                    }
                    results
                });
            } else {
                let reified_dsts = self.reify(dst, dst_method_id);
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if let Key::Var(_, access_path) = key {
                            let mut poisoned = false;
                            for reified_dst in &reified_dsts {
                                if reified_dst.base == access_path.base
                                    && reified_dst.fields.len() <= access_path.fields.len()
                                    && reified_dst.fields
                                        == access_path.fields[..reified_dst.fields.len()]
                                {
                                    results.insert(ConflictField::Field {
                                        container: *container,
                                        key: Key::All,
                                        read_only: *read_only,
                                    });
                                    poisoned = true;
                                    break;
                                }
                            }

                            if !poisoned {
                                results.insert(fact.clone());
                            }
                        } else {
                            results.insert(fact.clone());
                        }
                    }
                    results
                });
            }
        }

        let src = AccessPath::try_from(src.unwrap());
        if src.is_err() {
            return Self::identity();
        }
        let src = src.unwrap();

        let maybe_mut_borrowed = self.maybe_mut_borrowed.clone();
        if dst.fields.is_empty() && src.fields.is_empty() {
            return Box::new(move |fact| {
                let mut results = HashSet::new();
                if let ConflictField::Field {
                    container,
                    key,
                    read_only,
                } = fact
                {
                    if let Key::Var(_, access_path) = key {
                        if dst.base == access_path.base {
                            let key = if maybe_mut_borrowed[&src_method_id].contains(&src.base) {
                                Key::All
                            } else {
                                Key::Var(
                                    src_method_id,
                                    AccessPath {
                                        base: src.base,
                                        fields: access_path.fields.clone(),
                                    },
                                )
                            };
                            results.insert(ConflictField::Field {
                                container: *container,
                                key,
                                read_only: *read_only,
                            });
                        } else {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                }
                results
            });
        }

        if dst.fields.is_empty() && !src.fields.is_empty() {
            let reified_srcs = self.reify(src, src_method_id);
            return Box::new(move |fact| {
                let mut results = HashSet::new();
                if let ConflictField::Field {
                    container,
                    key,
                    read_only,
                } = fact
                {
                    if let Key::Var(_, access_path) = key {
                        if dst.base == access_path.base {
                            for reified_src in &reified_srcs {
                                let key = if maybe_mut_borrowed[&src_method_id]
                                    .contains(&reified_src.base)
                                {
                                    Key::All
                                } else {
                                    let mut composed_fields = reified_src.fields.clone();
                                    composed_fields.extend(access_path.fields.clone());
                                    Key::Var(
                                        src_method_id,
                                        AccessPath {
                                            base: reified_src.base,
                                            fields: composed_fields,
                                        },
                                    )
                                };
                                results.insert(ConflictField::Field {
                                    container: *container,
                                    key,
                                    read_only: *read_only,
                                });
                            }
                        } else {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                }
                results
            });
        }

        if !dst.fields.is_empty() && src.fields.is_empty() {
            let reified_dsts = self.reify(dst, dst_method_id);
            return Box::new(move |fact| {
                let mut results = HashSet::new();
                if let ConflictField::Field {
                    container,
                    key,
                    read_only,
                } = fact
                {
                    if let Key::Var(_, access_path) = key {
                        let mut all_propagated = true;
                        for reified_dst in &reified_dsts {
                            if reified_dst.base == access_path.base
                                && reified_dst.fields.len() <= access_path.fields.len()
                                && reified_dst.fields
                                    == access_path.fields[..reified_dst.fields.len()]
                            {
                                let key = if maybe_mut_borrowed[&src_method_id].contains(&src.base)
                                {
                                    Key::All
                                } else {
                                    Key::Var(
                                        src_method_id,
                                        AccessPath {
                                            base: src.base,
                                            fields: access_path.fields[reified_dst.fields.len()..]
                                                .to_vec(),
                                        },
                                    )
                                };
                                results.insert(ConflictField::Field {
                                    container: *container,
                                    key,
                                    read_only: *read_only,
                                });
                            } else {
                                all_propagated = false;
                            }
                        }

                        if !all_propagated {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                }
                results
            });
        }

        // For case: !dst.fields.is_empty() && !src.fields.is_empty(), in practice we never meet
        // assignments in this form(like `x.a.b.c = y.p.q.r`), even though it's legal in syntax
        // of MIR, that's still too crazy if this kind of assignments really exists...
        panic!(
            "unable to analyze the code you provided, please report this issue in \
                 https://github.com/WeBankBlockchain/liquid/issues"
        )
    }

    fn resolve_const_val(&self, const_val: &ConstValue<'tcx>) -> Option<Vec<u8>> {
        match const_val {
            ConstValue::Scalar(scalar) => {
                match scalar {
                    Scalar::Int(int) => {
                        // The first size bytes of data are the value.
                        // Do not try to read less or more bytes than that.
                        // The remaining bytes must be 0.
                        let size = int.size().bytes() as usize;
                        let data = if int == &ScalarInt::ZST {
                            0u128
                        } else {
                            int.to_bits(int.size()).unwrap()
                        };
                        let bytes = &data.to_le_bytes()[..size];
                        return Some(bytes.to_vec());
                    }
                    Scalar::Ptr(ptr) => match self.tcx.get_global_alloc(ptr.alloc_id) {
                        Some(GlobalAlloc::Memory(alloc)) => {
                            let alloc_len = alloc.len() as u64;
                            let offset = ptr.offset;
                            assert!(alloc_len > offset.bytes());
                            let size = alloc_len - offset.bytes();
                            if let Ok(bytes) = alloc.get_bytes(
                                &self.tcx,
                                AllocRange {
                                    start: offset,
                                    size: Size::from_bytes(size),
                                },
                            ) {
                                return Some(bytes.to_vec());
                            }
                        }
                        _ => (),
                    },
                }
            }
            ConstValue::Slice { data, start, end } => {
                assert!(end > start);
                if data.mutability == Mutability::Not {
                    let bytes = data.get_bytes(
                        &self.tcx,
                        AllocRange {
                            start: Size::from_bytes(*start),
                            size: Size::from_bytes(end - start),
                        },
                    );
                    if bytes.is_ok() {
                        return Some(bytes.unwrap().to_vec());
                    }
                }
            }
            unknown => debug!("resolve unknown type of constant: `{:?}`", unknown),
        }
        None
    }

    fn resolve_const(&self, constant: &Constant<'tcx>) -> Option<Vec<u8>> {
        let const_kind = &constant.literal;
        match const_kind {
            ConstantKind::Val(val, _) => {
                if let Some(resolved_val) = self.resolve_const_val(val) {
                    return Some(resolved_val);
                }
            }
            ConstantKind::Ty(constant) => match &constant.val {
                ConstKind::Unevaluated(unevaluated) => {
                    let param_env = ParamEnv::reveal_all();
                    if let Some(resolved_val) = self
                        .tcx
                        .const_eval_resolve(param_env, *unevaluated, None)
                        .and_then(|resolved| Ok(self.resolve_const_val(&resolved)))
                        .ok()
                        .flatten()
                    {
                        return Some(resolved_val);
                    }
                }
                ConstKind::Value(val) => {
                    if let Some(resolved_val) = self.resolve_const_val(val) {
                        return Some(resolved_val);
                    }
                }
                _ => (),
            },
        }
        None
    }
}

impl<'tcx, 'graph> IfdsProblem<'tcx> for ConflictFields<'tcx, 'graph> {
    type Icfg = BackwardCFG<'graph, 'tcx>;
    type Fact = ConflictField;

    fn zero_value() -> Self::Fact {
        ConflictField::Zero
    }

    fn initial_seeds(
        &mut self,
    ) -> HashMap<<Self::Icfg as InterproceduralCFG>::Node, HashSet<Self::Fact>> {
        let entrance = self.icfg.get_method_by_index(self.entry_point);
        self.insert_var_defs(entrance);
        let start_points = self.icfg.get_start_points_of(entrance);
        let mut initial_seeds: HashMap<_, _> = Default::default();
        for start_point in start_points {
            initial_seeds.insert(*start_point, HashSet::from_iter([Self::zero_value()]));
        }
        initial_seeds
    }

    fn get_call_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
    ) -> FlowFunction<'tcx, Self::Fact> {
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
                    Some((place, _)) => place,
                    _ => unreachable!(),
                };
                let src = match &args[0] {
                    Operand::Move(place) | Operand::Copy(place) => place,
                    _ => unreachable!(),
                };
                return self.process_assignment(dst, Some(src), caller_id, caller_id);
            }

            self.insert_var_defs(callee);

            if let Some((ret_place, _)) = destination {
                let ret_local = ret_place.local;
                return self.process_assignment(
                    &Place {
                        local: ret_local,
                        projection: self.tcx.intern_place_elems(&[]),
                    },
                    Some(&Place {
                        local: RETURN_PLACE,
                        projection: self.tcx.intern_place_elems(&[]),
                    }),
                    caller_id,
                    callee_id,
                );
            } else {
                Self::empty()
            }
        } else {
            unreachable!("the kind of terminator at call site must be `Call`")
        }
    }

    fn get_return_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        callee: &<Self::Icfg as InterproceduralCFG>::Method,
        _exit_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'tcx, Self::Fact> {
        if call_site.basic_block.is_none() {
            return Self::identity();
        }

        let caller = self.icfg.get_method_by_index(call_site.belongs_to);
        let basic_block = call_site.basic_block.unwrap();
        let call_site_bbd = &self.tcx.optimized_mir(caller.def_id).basic_blocks()[basic_block];
        let terminator = call_site_bbd.terminator.as_ref().unwrap();
        let caller_id = caller.def_id;

        if let TerminatorKind::Call { args, .. } = &terminator.kind {
            let actual_args = args
                .iter()
                .map(|arg| match arg {
                    Operand::Copy(place) | Operand::Move(place) => {
                        assert!(place.projection.is_empty());
                        Some(Either::Left(place.local))
                    }
                    Operand::Constant(box constant) => self
                        .resolve_const(constant)
                        .and_then(|constant| Some(Either::Right(constant))),
                })
                .collect::<Vec<_>>();
            let param_args = self
                .tcx
                .optimized_mir(callee.def_id)
                .args_iter()
                .collect::<Vec<_>>();
            assert_eq!(actual_args.len(), param_args.len());

            let maybe_mut_borrowed = self.maybe_mut_borrowed.clone();
            Box::new(move |fact| {
                let mut results = HashSet::new();
                if let ConflictField::Field {
                    container,
                    key,
                    read_only,
                } = fact
                {
                    if let Key::Var(_, access_path) = key {
                        if let Some(pos) =
                            param_args.iter().position(|arg| arg == &access_path.base)
                        {
                            let actual_arg = &actual_args[pos];
                            let key = if let Some(actual_arg) = actual_arg {
                                match actual_arg {
                                    Either::Left(local) => {
                                        if maybe_mut_borrowed[&caller_id].contains(&local) {
                                            Key::All
                                        } else {
                                            Key::Var(
                                                caller_id,
                                                AccessPath {
                                                    base: *local,
                                                    fields: access_path.fields.clone(),
                                                },
                                            )
                                        }
                                    }
                                    Either::Right(constant) => Key::Const(constant.clone()),
                                }
                            } else {
                                Key::All
                            };
                            results.insert(ConflictField::Field {
                                container: *container,
                                key,
                                read_only: *read_only,
                            });
                        } else {
                            results.insert(ConflictField::Field {
                                container: *container,
                                key: Key::All,
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
    ) -> FlowFunction<'tcx, Self::Fact> {
        if curr.basic_block.is_none() {
            return Self::identity();
        }

        let method = self.icfg.get_method_by_index(curr.belongs_to);
        let body = self.tcx.optimized_mir(method.def_id);
        let local_decls = &body.local_decls;
        let basic_block = curr.basic_block.unwrap();
        let bbd = &body.basic_blocks()[basic_block];
        let method_id = method.def_id;
        let maybe_mut_borrowed = self.maybe_mut_borrowed.clone();

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

            let dst = match destination {
                Some((place, _)) => place,
                _ => unreachable!(),
            };
            if callee.used_for_clone {
                // The reason why a method used for cloning coming into this position is that
                // that method must have no MIR body.
                let src = match &args[0] {
                    Operand::Move(place) | Operand::Copy(place) => place,
                    _ => unreachable!(),
                };
                return self.process_assignment(dst, Some(src), method_id, method_id);
            }

            let fn_name = KnownNames::get(self.tcx, callee.def_id);

            if matches!(
                fn_name,
                KnownNames::LiquidEnvGetCaller
                    | KnownNames::LiquidEnvGetOrigin
                    | KnownNames::LiquidEnvNow
                    | KnownNames::LiquidEnvGetAddress
                    | KnownNames::LiquidEnvGetBlockNumber
            ) {
                let env_key = Key::Env(fn_name.into());
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        container,
                        key,
                        read_only,
                    } = fact
                    {
                        if let Key::Var(_, access_path) = key {
                            if access_path.base == dst.local {
                                let new_fact = ConflictField::Field {
                                    container: *container,
                                    key: env_key.clone(),
                                    read_only: *read_only,
                                };
                                results.insert(new_fact);
                                return results;
                            }
                        }
                    }
                    results.insert(fact.clone());
                    return results;
                });
            }

            // Special functions that needs results of pointer analysis.
            if matches!(
                fn_name,
                KnownNames::LiquidStorageCollectionsMappingContainsKey
                    | KnownNames::LiquidStorageCollectionsMappingExtend
                    | KnownNames::LiquidStorageCollectionsMappingGet
                    | KnownNames::LiquidStorageCollectionsMappingGetMut
                    | KnownNames::LiquidStorageCollectionsMappingIndex
                    | KnownNames::LiquidStorageCollectionsMappingIndexMut
                    | KnownNames::LiquidStorageCollectionsMappingInsert
                    | KnownNames::LiquidStorageCollectionsMappingLen
                    | KnownNames::LiquidStorageCollectionsMappingMutateWith
                    | KnownNames::LiquidStorageCollectionsMappingRemove
                    | KnownNames::LiquidStorageCollectionsMappingIsEmpty
                    | KnownNames::LiquidStorageValueGet
                    | KnownNames::LiquidStorageValueGetMut
                    | KnownNames::LiquidStorageValueMutateWith
                    | KnownNames::LiquidStorageValueSet
                    | KnownNames::LiquidStorageCollectionsVecUse
                    | KnownNames::LiquidStorageCollectionsIterableMappingUse
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
                        KnownNames::LiquidStorageValueGet
                            | KnownNames::LiquidStorageValueGetMut
                            | KnownNames::LiquidStorageValueMutateWith
                            | KnownNames::LiquidStorageValueSet
                    ) {
                        let this = &args[0];
                        let read_only = match this.ty(local_decls, self.tcx).kind() {
                            TyKind::Ref(_, _, mutable) => mutable != &Mutability::Mut,
                            _ => unreachable!(),
                        };

                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in &states {
                                    let new_fact = ConflictField::Field {
                                        container: *container,
                                        key: Key::All,
                                        read_only,
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
                        KnownNames::LiquidStorageCollectionsMappingContainsKey
                            | KnownNames::LiquidStorageCollectionsMappingGet
                            | KnownNames::LiquidStorageCollectionsMappingIndex
                            | KnownNames::LiquidStorageCollectionsMappingGetMut
                            | KnownNames::LiquidStorageCollectionsMappingIndexMut
                            | KnownNames::LiquidStorageCollectionsMappingMutateWith
                    ) {
                        let this = &args[0];
                        let read_only = match this.ty(local_decls, self.tcx).kind() {
                            TyKind::Ref(_, _, mutable) => mutable != &Mutability::Mut,
                            _ => unreachable!(),
                        };
                        let key_local = match &args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in &states {
                                    let key = if maybe_mut_borrowed[&method_id].contains(&key_local)
                                    {
                                        Key::All
                                    } else {
                                        Key::Var(
                                            method_id,
                                            AccessPath {
                                                base: key_local,
                                                fields: vec![],
                                            },
                                        )
                                    };
                                    let new_fact = ConflictField::Field {
                                        container: *container,
                                        key,
                                        read_only,
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
                        KnownNames::LiquidStorageCollectionsMappingInsert
                            | KnownNames::LiquidStorageCollectionsMappingRemove
                    ) {
                        if let Operand::Constant(box constant) = &args[1] {
                            let key = if let Some(constant) = self.resolve_const(constant) {
                                Key::Const(constant)
                            } else {
                                Key::All
                            };

                            return Box::new(move |fact| {
                                if fact == &ConflictField::Zero {
                                    let mut results = HashSet::new();
                                    for container in &states {
                                        results.insert(ConflictField::Field {
                                            container: *container,
                                            key: key.clone(),
                                            read_only: false,
                                        });
                                        results.insert(ConflictField::Field {
                                            container: *container,
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

                        let key_local = match &args[1] {
                            Operand::Copy(place) | Operand::Move(place) => place.local,
                            _ => unreachable!(),
                        };
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in &states {
                                    let key = if maybe_mut_borrowed[&method_id].contains(&key_local)
                                    {
                                        Key::All
                                    } else {
                                        Key::Var(
                                            method_id,
                                            AccessPath {
                                                base: key_local,
                                                fields: vec![],
                                            },
                                        )
                                    };

                                    results.insert(ConflictField::Field {
                                        container: *container,
                                        key,
                                        read_only: false,
                                    });
                                    results.insert(ConflictField::Field {
                                        container: *container,
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

                    if matches!(fn_name, KnownNames::LiquidStorageCollectionsMappingExtend) {
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in &states {
                                    results.insert(ConflictField::Field {
                                        container: *container,
                                        key: Key::All,
                                        read_only: false,
                                    });
                                    results.insert(ConflictField::Field {
                                        container: *container,
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

                    if matches!(
                        fn_name,
                        KnownNames::LiquidStorageCollectionsMappingLen
                            | KnownNames::LiquidStorageCollectionsMappingIsEmpty
                            | KnownNames::LiquidStorageCollectionsVecUse
                            | KnownNames::LiquidStorageCollectionsIterableMappingUse
                    ) {
                        return Box::new(move |fact| {
                            if fact == &ConflictField::Zero {
                                let mut results = HashSet::new();
                                for container in &states {
                                    results.insert(ConflictField::Field {
                                        container: *container,
                                        key: Key::Len,
                                        read_only: matches!(fn_name,
                                            KnownNames::LiquidStorageCollectionsMappingLen
                                            | KnownNames::LiquidStorageCollectionsMappingIsEmpty),
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
                return Self::identity();
            }
        } else {
            let statements = &bbd.statements;
            let assignments: Vec<Either<FlowFunction<'tcx, Self::Fact>, (Place<'tcx>, Vec<u8>)>> =
                statements
                    .iter()
                    .filter_map(|stmt| {
                        let kind = &stmt.kind;
                        if let StatementKind::Assign(box (l_place, r_value)) = kind {
                            match r_value {
                                Rvalue::Use(r_operand) => match r_operand {
                                    Operand::Move(r_place) | Operand::Copy(r_place) => {
                                        let flow_fn = self.process_assignment(
                                            l_place,
                                            Some(r_place),
                                            method_id,
                                            method_id,
                                        );
                                        return Some(Either::Left(flow_fn));
                                    }
                                    Operand::Constant(box constant) => {
                                        if let Some(constant) = self.resolve_const(constant) {
                                            return Some(Either::Right((
                                                l_place.clone(),
                                                constant,
                                            )));
                                        }
                                    }
                                },
                                Rvalue::Ref(_, kind, r_place) => {
                                    if kind == &BorrowKind::Shared {
                                        let flow_fn = self.process_assignment(
                                            l_place,
                                            Some(r_place),
                                            method_id,
                                            method_id,
                                        );
                                        return Some(Either::Left(flow_fn));
                                    }
                                }
                                _ => (),
                            }
                            Some(Either::Left(
                                self.process_assignment(l_place, None, method_id, method_id),
                            ))
                        } else {
                            None
                        }
                    })
                    .rev()
                    .collect::<Vec<_>>();

            Box::new(move |fact| {
                let mut results = HashSet::from_iter([fact.clone()]);
                for item in &assignments {
                    match item {
                        Either::Left(flow_fn) => {
                            let facts = results.drain().collect::<Vec<_>>();
                            for fact in facts {
                                let facts = flow_fn(&fact);
                                if !facts.is_empty() {
                                    results.extend(facts);
                                } else {
                                    results.insert(fact);
                                }
                            }
                        }
                        Either::Right((l_place, constant)) => {
                            let facts = results.drain().collect::<Vec<_>>();
                            for fact in facts {
                                if let ConflictField::Field {
                                    container,
                                    key: Key::Var(_, access_path),
                                    read_only,
                                } = &fact
                                {
                                    if let Ok(l_ap) = AccessPath::try_from(l_place) {
                                        if access_path == &l_ap {
                                            results.insert(ConflictField::Field {
                                                container: *container,
                                                key: Key::Const(constant.clone()),
                                                read_only: *read_only,
                                            });
                                        } else {
                                            results.insert(fact);
                                        }
                                    } else {
                                        results.insert(fact);
                                    }
                                } else {
                                    results.insert(fact);
                                }
                            }
                        }
                    }
                }
                results
            })
        }
    }

    fn get_call_to_return_flow_function(
        &mut self,
        call_site: &<Self::Icfg as InterproceduralCFG>::Node,
        _return_site: &<Self::Icfg as InterproceduralCFG>::Node,
    ) -> FlowFunction<'tcx, Self::Fact> {
        if call_site.basic_block.is_none() {
            return Self::identity();
        }

        let method = self.icfg.get_method_by_index(call_site.belongs_to);
        let body = self.tcx.optimized_mir(method.def_id);
        let basic_block = call_site.basic_block.unwrap();
        let bbd = &body.basic_blocks()[basic_block];
        let terminator = bbd.terminator.as_ref().unwrap();

        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
            if let Some((ret_place, _)) = destination {
                let ret_local = ret_place.local;
                return Box::new(move |fact| {
                    let mut results = HashSet::new();
                    if let ConflictField::Field {
                        key: Key::Var(_, access_path),
                        ..
                    } = fact
                    {
                        if access_path.base != ret_local {
                            results.insert(fact.clone());
                        }
                    } else {
                        results.insert(fact.clone());
                    }
                    results
                });
            } else {
                Self::identity()
            }
        } else {
            unreachable!("the kind of terminator at call site must be `Call`")
        }
    }
}
