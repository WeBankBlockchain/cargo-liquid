use rustc_middle::ty::{
    subst::{GenericArgKind, SubstsRef},
    TyKind,
};

use rustc_middle::ty::ProjectionTy;
pub fn is_concrete(ty: &TyKind<'_>) -> bool {
    match ty {
        TyKind::Adt(_, gen_args)
        | TyKind::Closure(_, gen_args)
        | TyKind::FnDef(_, gen_args)
        | TyKind::Generator(_, gen_args, _)
        | TyKind::Opaque(_, gen_args)
        | TyKind::Projection(ProjectionTy {
            substs: gen_args, ..
        })
        | TyKind::Tuple(gen_args) => are_concrete(gen_args),
        TyKind::Bound(..)
        | TyKind::Dynamic(..)
        | TyKind::Error(..)
        | TyKind::Infer(..)
        | TyKind::Param(..) => false,
        TyKind::Ref(_, ty, _) => is_concrete(ty.kind()),
        _ => true,
    }
}

pub fn are_concrete(gen_args: SubstsRef<'_>) -> bool {
    for gen_arg in gen_args.iter() {
        if let GenericArgKind::Type(ty) = gen_arg.unpack() {
            if !is_concrete(ty.kind()) {
                return false;
            }
        }
    }
    true
}
