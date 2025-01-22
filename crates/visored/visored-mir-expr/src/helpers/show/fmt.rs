use crate::{
    expr::{application::VdMirFunc, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx},
    hint::{VdMirHintIdx, VdMirHintIdxRange},
    stmt::{VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdx, VdMirStmtIdxRange},
    symbol::local_defn::{storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead},
};
use eterned::db::EternerDb;
use husky_tree_utils::display::DisplayTree;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};
use visored_term::term::literal::VdLiteralData;

pub struct VdMirExprFormatter<'a> {
    db: &'a EternerDb,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
    local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
}

impl<'a> VdMirExprFormatter<'a> {
    pub fn new(
        db: &'a EternerDb,
        expr_arena: VdMirExprArenaRef<'a>,
        stmt_arena: VdMirStmtArenaRef<'a>,
        local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
            local_defn_storage,
        }
    }
}

impl<'a> VdMirExprFormatter<'a> {
    pub fn db(&self) -> &'a EternerDb {
        self.db
    }
}

impl<'a> VdMirExprFormatter<'a> {
    pub fn show_fmt_expr_ext(
        &self,
        expr: VdMirExprIdx,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.show_fmt_expr(expr, VdPrecedenceRange::ANY, f)
    }

    pub fn show_fmt_expr(
        &self,
        expr: VdMirExprIdx,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        if precedence_range.contains(self.expr_arena[expr].data().outer_precedence()) {
            self.show_fmt_inner(expr, f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(expr, f)?;
            f.write_str(")")
        }
    }

    fn show_fmt_inner(
        &self,
        expr: VdMirExprIdx,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match *self.expr_arena[expr].data() {
            VdMirExprData::Literal(literal) => literal.show(f),
            VdMirExprData::Variable(local_defn) => {
                match *self.local_defn_storage.defn_arena()[local_defn].head() {
                    VdMirSymbolLocalDefnHead::Letter(lx_math_letter) => {
                        write!(f, "{}", lx_math_letter.unicode())
                    }
                }
            }
            VdMirExprData::Application {
                function,
                arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(signature) => match signature.opr {
                    VdMirBasePrefixOpr::RingPos => {
                        f.write_str("+")?;
                        self.show_fmt_expr(arguments.first().unwrap(), VdPrecedenceRange::ATOM, f)
                    }
                    VdMirBasePrefixOpr::RingNeg => {
                        f.write_str("-")?;
                        self.show_fmt_expr(arguments.first().unwrap(), VdPrecedenceRange::ATOM, f)
                    }
                    _ => todo!(),
                },
                VdMirFunc::NormalBaseSeparator(signature) => todo!(),
                VdMirFunc::NormalBaseBinaryOpr(signature) => {
                    let opr = signature.opr;
                    self.show_fmt_expr(arguments.first().unwrap(), opr.left_precedence_range(), f)?;
                    f.write_str(" ")?;
                    f.write_str(opr.unicode())?;
                    f.write_str(" ")?;
                    self.show_fmt_expr(arguments.last().unwrap(), opr.right_precedence_range(), f)?;
                    Ok(())
                }
                VdMirFunc::Power(signature) => {
                    use num_traits::cast::ToPrimitive;

                    match *self.expr_arena[arguments.last().unwrap()].data() {
                        VdMirExprData::Literal(literal) => match *literal.data() {
                            VdLiteralData::Int(ref i)
                                if let Some(i) = i.to_i128()
                                    && i >= 0
                                    && i < 10 =>
                            {
                                use husky_unicode_symbols::superscript::superscript;

                                // use unicode to show the superscript
                                let superscript = superscript(i as u8).unwrap();
                                self.show_fmt_expr(
                                    arguments.first().unwrap(),
                                    VdPrecedenceRange::ATOM,
                                    f,
                                )?;
                                write!(f, "{}", superscript)?;
                                return Ok(());
                            }
                            VdLiteralData::Frac(ref frac) if frac.is_frac128(1, 2) => {
                                f.write_str("√")?;
                                self.show_fmt_expr(
                                    arguments.first().unwrap(),
                                    VdPrecedenceRange::ATOM,
                                    f,
                                )?;
                                return Ok(());
                            }
                            _ => (),
                        },
                        _ => (),
                    }
                    self.show_fmt_expr(arguments.first().unwrap(), VdPrecedenceRange::ATOM, f)?;
                    write!(f, "^{{")?;
                    self.show_fmt_expr(arguments.last().unwrap(), VdPrecedenceRange::ANY, f)?;
                    f.write_str("}}")
                }
                VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => {
                    f.write_str("√")?;
                    self.show_fmt_expr(arguments.first().unwrap(), VdPrecedenceRange::ATOM, f)
                }
            },
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                let signature = followers.first().unwrap().0;
                let precedence_range = signature.separator().left_precedence_range();
                self.show_fmt_expr(leader, precedence_range, f)?;
                for &(func, follower) in followers {
                    f.write_str(" ")?;
                    signature.separator().show_fmt(f)?;
                    f.write_str(" ")?;
                    self.show_fmt_expr(follower, precedence_range, f)?;
                }
                Ok(())
            }
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => {
                let signature = followers.first().unwrap().0;
                let precedence_range = signature.separator().left_precedence_range();
                self.show_fmt_expr(leader, precedence_range, f)?;
                for &(func, follower) in followers {
                    f.write_str(" ")?;
                    signature.separator().show_fmt(f)?;
                    f.write_str(" ")?;
                    self.show_fmt_expr(follower, precedence_range, f)?;
                }
                Ok(())
            }
            VdMirExprData::ItemPath(path) => path.show_fmt(f),
        }
    }
}

impl VdMirExprData {
    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdMirExprData::Literal(vd_literal) => VdPrecedence::ATOM,
            VdMirExprData::Variable(arena_idx) => VdPrecedence::ATOM,
            VdMirExprData::Application {
                function,
                arguments,
            } => function.outer_precedence(),
            VdMirExprData::FoldingSeparatedList { leader, followers } => {
                followers[0].0.separator().outer_precedence()
            }
            VdMirExprData::ChainingSeparatedList {
                leader,
                followers,
                joined_signature,
            } => followers.first().unwrap().0.separator().outer_precedence(),
            VdMirExprData::ItemPath(vd_item_path) => VdPrecedence::ATOM,
        }
    }
}
