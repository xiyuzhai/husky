pub mod attach;
pub mod binary;
pub mod literal;
pub mod notation;
pub mod prefix;
pub mod suffix;
pub mod uniadic_array;
pub mod uniadic_chain;
pub mod variadic_array;
pub mod variadic_chain;

use self::{attach::AttachDispatch, binary::VdSemBinaryDispatch};
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use literal::VdSemLiteralDispatch;
use visored_opr::opr::binary::VdBinaryOpr;
use visored_zfs_ty::term::literal::VdZfsLiteral;

/// It's a tree of both form and meaning
#[derive(Debug, PartialEq, Eq)]
pub enum VdSemExprData {
    Literal {
        literal: VdZfsLiteral,
        dispatch: VdSemLiteralDispatch,
    },
    Notation,
    Binary {
        lopd: VdSemExprIdx,
        opr: VdBinaryOpr,
        ropd: VdSemExprIdx,
        dispatch: VdSemBinaryDispatch,
    },
    Prefix {
        opr: VdSemExprIdx,
        opd: VdSemExprIdx,
        dispatch: (),
    },
    Suffix {
        opd: VdSemExprIdx,
        opr: VdSemExprIdx,
        dispatch: (),
    },
    Attach {
        base: VdSemExprIdx,
        // INVARIANCE: at least one of these are some
        top: Option<VdSemExprIdx>,
        bottom: Option<VdSemExprIdx>,
        top_left: Option<VdSemExprIdx>,
        bottom_left: Option<VdSemExprIdx>,
        top_right: Option<VdSemExprIdx>,
        bottom_right: Option<VdSemExprIdx>,
        dispatch: AttachDispatch,
    },
    UniadicChain,
    VariadicChain,
    UniadicArray,
    VariadicArray,
}

pub type VdSemExprIdx = ArenaIdx<VdSemExprData>;
pub type VdSemExprIdxRange = ArenaIdxRange<VdSemExprData>;
pub type VdSemExprArena = Arena<VdSemExprData>;
pub type VdSemExprArenaRef<'a> = ArenaRef<'a, VdSemExprData>;
