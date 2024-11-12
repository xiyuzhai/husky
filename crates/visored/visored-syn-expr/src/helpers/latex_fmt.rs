use super::*;
use crate::{
    clause::{VdSynClauseArenaRef, VdSynClauseData, VdSynClauseIdx},
    expr::{VdSynExprArenaRef, VdSynExprData, VdSynExprIdx},
    phrase::{
        noun::VdSynNounPhraseData, VdSynPhrase, VdSynPhraseArenaRef, VdSynPhraseData,
        VdSynPhraseIdx,
    },
    sentence::{VdSynSentenceArenaRef, VdSynSentenceData, VdSynSentenceIdx, VdSynSentenceIdxRange},
};
use either::*;
use expr::VdSynBinaryOpr;
use latex_token::idx::LxTokenIdxRange;
use sentence::VdSynSentenceEnd;
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_zfc_ty::{menu::vd_zfc_ty_menu, term::literal::VdZfcLiteralData};

pub struct VdSynExprLaTeXFormatter<'a> {
    db: &'a ::salsa::Db,
    expr_arena: VdSynExprArenaRef<'a>,
    phrase_arena: VdSynPhraseArenaRef<'a>,
    clause_arena: VdSynClauseArenaRef<'a>,
    sentence_arena: VdSynSentenceArenaRef<'a>,
    result: String,
}

impl<'a> VdSynExprLaTeXFormatter<'a> {
    pub fn new(
        db: &'a ::salsa::Db,
        expr_arena: VdSynExprArenaRef<'a>,
        phrase_arena: VdSynPhraseArenaRef<'a>,
        clause_arena: VdSynClauseArenaRef<'a>,
        sentence_arena: VdSynSentenceArenaRef<'a>,
    ) -> Self {
        Self {
            db,
            expr_arena,
            phrase_arena,
            clause_arena,
            sentence_arena,
            result: Default::default(),
        }
    }

    pub fn fmt_sentences(&mut self, sentences: VdSynSentenceIdxRange) {
        for sentence_idx in sentences {
            self.fmt_sentence(sentence_idx);
            self.result.push_str("\n\n");
        }
    }

    pub fn fmt_sentence(&mut self, sentence_idx: VdSynSentenceIdx) {
        match self.sentence_arena[sentence_idx] {
            VdSynSentenceData::Clauses { clauses, end } => {
                for (index, clause_idx) in clauses.into_iter().enumerate() {
                    self.fmt_clause(clause_idx);
                }
                match end {
                    VdSynSentenceEnd::Period(_) => self.result += ".",
                }
            }
        }
    }

    pub fn fmt_clause(&mut self, clause_idx: VdSynClauseIdx) {
        match self.clause_arena[clause_idx] {
            VdSynClauseData::Let { .. } => todo!(),
            VdSynClauseData::Assume {
                assume_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => todo!(),
            VdSynClauseData::Then { formula, .. } => todo!(),
        }
    }

    pub fn fmt_phrase(&mut self, phrase_idx: VdSynPhraseIdx) {
        match self.phrase_arena[phrase_idx] {
            VdSynPhraseData::Noun(ref vd_syn_noun_phrase_data) => todo!(),
        }
    }

    fn fmt_noun_phrase(&mut self, noun_phrase: &VdSynNounPhraseData) {
        // Implement noun phrase formatting
        // This is a placeholder implementation
        // self.result.push_str("\\textbf{");
        // self.fmt_expr(noun_phrase.head);
        // self.result.push('}');
        todo!()
    }

    pub fn fmt_expr(&mut self, expr_idx: VdSynExprIdx) {
        let db = self.db;
        match self.expr_arena[expr_idx] {
            VdSynExprData::Literal { literal, .. } => match literal.data(db) {
                VdZfcLiteralData::NaturalNumber(s) => {
                    if self
                        .result
                        .chars()
                        .last()
                        .map_or(false, |c| c.is_alphanumeric())
                    {
                        self.result.push(' ');
                    }
                    self.result.push_str(s);
                }
                VdZfcLiteralData::NegativeInteger(_) => todo!(),
                VdZfcLiteralData::FiniteDecimalRepresentation(_) => {
                    todo!()
                }
                VdZfcLiteralData::SpecialConstant(vd_zfc_special_constant) => todo!(),
            },
            VdSynExprData::Letter { letter, .. } => {
                self.result += letter.latex_code();
            }
            VdSynExprData::Binary {
                lopd, opr, ropd, ..
            } => {
                self.fmt_expr(lopd);
                match opr {
                    VdSynBinaryOpr::Base(_, opr) => self.result.push_str(opr.latex_code()),
                    VdSynBinaryOpr::Composite(opr, _) => self.fmt_expr(opr),
                }
                self.fmt_expr(ropd);
            }
            VdSynExprData::Prefix { opr, opd } => todo!(),
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::Attach { .. } => todo!(),
            VdSynExprData::UniadicChain => todo!(),
            VdSynExprData::VariadicChain => todo!(),
            VdSynExprData::UniadicArray => todo!(),
            VdSynExprData::VariadicArray => todo!(),
            VdSynExprData::BaseOpr { opr } => todo!(),
            VdSynExprData::Err(ref error) => unreachable!("{error}"),
            VdSynExprData::SeparatedList { .. } => todo!(),
            VdSynExprData::LxDelimited { .. } => todo!(),
            VdSynExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => todo!(),
            VdSynExprData::Fraction {
                numerator,
                denominator,
                ..
            } => todo!(),
            VdSynExprData::Sqrt { radicand, .. } => todo!(),
        }
    }

    pub fn finish(self) -> String {
        self.result
    }
}

#[test]
#[ignore]
fn latex_fmt_works() {
    // let db = &DB::default();
    // let menu = vd_zfc_ty_menu(db);
    // let mut builder = VdSynExprTestBuilder::new(db);
    // let one = builder.new_expr_checked(
    //     VdSynExprData::Literal {
    //         literal: menu.one_literal(),
    //         token_idx_range: todo!(),
    //     },
    //     "1",
    // );
    // let one_add_one = builder.new_expr_checked(
    //     VdSynExprData::Binary {
    //         lopd: one,
    //         opr: todo!(),
    //         // (VdBaseBinaryOpr::Add),
    //         ropd: one,
    //     },
    //     "1+1",
    // );
}
