//! In full generality, patterns are boolean functions over a type.
//!
//! Here our `pattern` means a boolean function over a certain type in mathematics
//!
//! ```latex
//! Let $x\in \mathbb{N}$.
//! ```
//!
//! In the above, $x$ is a trivial letter pattern over the natural numbers.

use crate::{symbol::local_defn::VdMirSymbolLocalDefnIdx, *};
use latex_math_letter::letter::LxMathLetter;
use visored_sem_expr::pattern::VdSemPattern;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirPattern {
    Letter {
        letter: LxMathLetter,
        symbol_local_defn: VdMirSymbolLocalDefnIdx,
    },
}

impl ToVdMir<VdMirPattern> for &VdSemPattern {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirPattern {
        match *self {
            VdSemPattern::Letter {
                token_idx_range,
                letter,
                local_defn,
            } => VdMirPattern::Letter {
                letter,
                symbol_local_defn: local_defn.to_vd_mir(builder),
            },
        }
    }
}
