#[allow(unused_imports)]
use log::*;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use std::ops::Deref;
use DefPathData::*;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum KnownNames {
    CoreOpsFunctionFnCall,
    CoreOpsFunctionFnCallMut,
    CoreOpsFunctionFnOnceCallOnce,
    RustAlloc,
    LiquidIntrinsicsRequire,
    LiquidStorageCollectionsMappingInitialize,
    LiquidStorageCollectionsMappingLen,
    LiquidStorageCollectionsMappingInsert,
    LiquidStorageCollectionsMappingContainsKey,
    LiquidStorageCollectionsMappingIndex,
    LiquidStorageCollectionsMappingIndexMut,
    LiquidStorageCollectionsMappingGet,
    LiquidStorageCollectionsMappingGetMut,
    LiquidEnvGetCaller,
    LiquidEnvGetOrigin,
    LiquidEnvNow,
    LiquidEnvGetAddress,
    LiquidEnvGetBlockNumber,
    None,
}

type PathIter<'a> = std::slice::Iter<'a, DisambiguatedDefPathData>;

impl KnownNames {
    pub fn get(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let crate_name = tcx.crate_name(def_id.krate);
        let data_path = &tcx.def_path(def_id);
        let path_iter = data_path.data.iter();
        match crate_name.as_str().deref() {
            "alloc" => Self::get_known_name_for_alloc_crate(path_iter),
            "core" => Self::get_known_name_for_core_crate(path_iter),
            "liquid_lang" => Self::get_known_name_for_liquid_crate(path_iter),
            _ => KnownNames::None,
        }
    }

    fn get_known_name_for_alloc_crate(mut _path_iter: PathIter<'_>) -> Self {
        // Ignores all allocating operations such as `__rust_alloc`, `__rust__dealloc`, etc.
        // For now we don't modeling the behavior of heap allocation.
        Self::RustAlloc
    }

    fn get_known_name_for_core_crate(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|name| match name.as_str().deref() {
                "ops" => Self::get_known_name_for_core_ops(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_ops_function_namespace(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "Fn" | "FnMut" | "FnOnce" => Self::get_def_data_path_elem_name(path_iter.next())
                    .map(|n| match n.as_str().deref() {
                        "call" => KnownNames::CoreOpsFunctionFnCall,
                        "call_mut" => KnownNames::CoreOpsFunctionFnCallMut,
                        "call_once" => KnownNames::CoreOpsFunctionFnOnceCallOnce,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_core_ops(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "function" => Self::get_known_name_for_ops_function_namespace(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_crate(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|name| match name.as_str().deref() {
                "intrinsics" => Self::get_known_name_for_liquid_intrinsics(path_iter),
                "lang_core" => Self::get_known_name_for_liquid_core(path_iter),
                "env_access" => Self::get_known_name_for_liquid_env(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_intrinsics(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "require" => KnownNames::LiquidIntrinsicsRequire,
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_core(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "storage" => Self::get_known_name_for_liquid_storage(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_env(mut path_iter: PathIter<'_>) -> Self {
        if let Some(DisambiguatedDefPathData { data: Impl, .. }) = path_iter.next() {
            Self::get_def_data_path_elem_name(path_iter.next())
                .map(|n| match n.as_str().deref() {
                    "get_caller" => KnownNames::LiquidEnvGetCaller,
                    "get_tx_origin" => KnownNames::LiquidEnvGetOrigin,
                    "now" => KnownNames::LiquidEnvNow,
                    "get_address" => KnownNames::LiquidEnvGetAddress,
                    "get_block_number" => KnownNames::LiquidEnvGetBlockNumber,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        } else {
            KnownNames::None
        }
    }

    fn get_known_name_for_liquid_storage(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "collections" => Self::get_known_name_for_liquid_collections(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_collections(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "mapping" => Self::get_known_name_for_liquid_mapping(path_iter),
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_known_name_for_liquid_mapping(mut path_iter: PathIter<'_>) -> Self {
        Self::get_def_data_path_elem_name(path_iter.next())
            .map(|n| match n.as_str().deref() {
                "impls" => {
                    if let Some(DisambiguatedDefPathData { data: Impl, .. }) = path_iter.next() {
                        Self::get_def_data_path_elem_name(path_iter.next())
                            .map(|n| match n.as_str().deref() {
                                "initialize" => {
                                    KnownNames::LiquidStorageCollectionsMappingInitialize
                                }
                                "len" => KnownNames::LiquidStorageCollectionsMappingLen,
                                "insert" => KnownNames::LiquidStorageCollectionsMappingInsert,
                                "contains_key" => {
                                    KnownNames::LiquidStorageCollectionsMappingContainsKey
                                }
                                "index" => KnownNames::LiquidStorageCollectionsMappingIndex,
                                "index_mut" => KnownNames::LiquidStorageCollectionsMappingIndexMut,
                                "get" => KnownNames::LiquidStorageCollectionsMappingGet,
                                "get_mut" => KnownNames::LiquidStorageCollectionsMappingGetMut,
                                _ => KnownNames::None,
                            })
                            .unwrap_or(KnownNames::None)
                    } else {
                        KnownNames::None
                    }
                }
                _ => KnownNames::None,
            })
            .unwrap_or(KnownNames::None)
    }

    fn get_def_data_path_elem_name(
        def_path_data_elem: Option<&DisambiguatedDefPathData>,
    ) -> Option<Symbol> {
        def_path_data_elem.and_then(|ref elem| {
            let DisambiguatedDefPathData { data, .. } = elem;
            match &data {
                TypeNs(name) | ValueNs(name) => Some(*name),
                _ => None,
            }
        })
    }
}
