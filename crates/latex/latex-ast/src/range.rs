use latex_token::idx::LxTokenIdxRange;

use crate::ast::{
    math::{
        LxMathAstArenaMap, LxMathAstData, LxMathAstIdx, LxMathAstIdxRange, LxMathCommandArgument,
    },
    rose::{LxRoseAstArenaMap, LxRoseAstData, LxRoseAstIdx},
    LxAstArena, LxAstArenaMap, LxAstArenaRef, LxAstData, LxAstIdx,
};

#[derive(Debug)]
pub struct LxAstTokenIdxRangeMap {
    pub(crate) math: LxMathAstArenaMap<LxTokenIdxRange>,
    pub(crate) rose: LxRoseAstArenaMap<LxTokenIdxRange>,
}

impl std::ops::Index<LxMathAstIdx> for LxAstTokenIdxRangeMap {
    type Output = LxTokenIdxRange;

    fn index(&self, index: LxMathAstIdx) -> &Self::Output {
        &self.math[index]
    }
}

impl std::ops::Index<LxRoseAstIdx> for LxAstTokenIdxRangeMap {
    type Output = LxTokenIdxRange;

    fn index(&self, index: LxRoseAstIdx) -> &Self::Output {
        &self.rose[index]
    }
}

impl LxAstTokenIdxRangeMap {
    pub fn math_asts_token_idx_range(&self, asts: LxMathAstIdxRange) -> LxTokenIdxRange {
        todo!()
    }
}

pub fn calc_ast_token_idx_range_map(db: &salsa::Db, arena: &LxAstArena) -> LxAstTokenIdxRangeMap {
    let mut calculator = LxAstTokenIdxRangeCalculator::new(db, arena);
    calculator.infer_all();
    LxAstTokenIdxRangeMap {
        math: calculator.math_data,
        rose: calculator.rose_data,
    }
}

struct LxAstTokenIdxRangeCalculator<'a> {
    db: &'a ::salsa::Db,
    ast_arena: LxAstArenaRef<'a>,
    math_data: LxMathAstArenaMap<LxTokenIdxRange>,
    rose_data: LxRoseAstArenaMap<LxTokenIdxRange>,
}

impl<'a> LxAstTokenIdxRangeCalculator<'a> {
    fn new(db: &'a ::salsa::Db, arena: &'a LxAstArena) -> Self {
        Self {
            db,
            ast_arena: arena.as_arena_ref(),
            math_data: LxMathAstArenaMap::new(&arena.math),
            rose_data: LxRoseAstArenaMap::new(&arena.rose),
        }
    }
}

impl<'a> LxAstTokenIdxRangeCalculator<'a> {
    fn infer_all(&mut self) {
        self.ast_arena.math().indexed_iter().for_each(|(idx, ast)| {
            self.infer_math_ast(idx, ast);
        });
        self.ast_arena.rose().indexed_iter().for_each(|(idx, ast)| {
            self.rose_data.insert_new(idx, self.calc_rose_ast(ast));
        });
    }

    fn infer_math_ast(&mut self, idx: LxMathAstIdx, ast: &LxMathAstData) {
        if !self.math_data.has(idx) {
            let range = self.calc_math_ast(ast);
            self.math_data.insert_new(idx, range);
        }
    }

    fn calc_math_ast(&mut self, data: &LxMathAstData) -> LxTokenIdxRange {
        match *data {
            LxMathAstData::PlainLetter(idx, _) => LxTokenIdxRange::new_single(*idx),
            LxMathAstData::StyledLetter {
                style_command_token_idx,
                style_rcurl_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*style_command_token_idx, *style_rcurl_token_idx),
            LxMathAstData::Punctuation(idx, _) => LxTokenIdxRange::new_single(*idx),
            LxMathAstData::Digit(idx, _) => LxTokenIdxRange::new_single(*idx),
            LxMathAstData::TextEdit { ref buffer } => todo!(),
            LxMathAstData::Attach { base, ref scripts } => {
                let mut range = self.get_math_ast_range(base);
                for &(_, script) in scripts {
                    let script_range = self.get_math_ast_range(script);
                    range = range.join(script_range);
                }
                range
            }
            LxMathAstData::Delimited {
                left_delimiter_token_idx,
                left_delimiter,
                asts,
                right_delimiter_token_idx,
                right_delimiter,
            } => LxTokenIdxRange::new_closed(*left_delimiter_token_idx, *right_delimiter_token_idx),
            LxMathAstData::CompleteCommand {
                command_token_idx,
                command_path,
                ref arguments,
            } => match arguments.last() {
                Some(last_argument) => LxTokenIdxRange::new_closed(
                    *command_token_idx,
                    *last_argument.rcurl_token_idx(),
                ),
                None => LxTokenIdxRange::new_single(*command_token_idx),
            },
            LxMathAstData::Environment {
                begin_command_token_idx,
                end_rcurl_token_idx,
                ..
            } => LxTokenIdxRange::new_closed(*begin_command_token_idx, *end_rcurl_token_idx),
        }
    }

    fn get_math_ast_range(&mut self, idx: LxMathAstIdx) -> LxTokenIdxRange {
        self.infer_math_ast(idx, &self.ast_arena.math()[idx]);
        self.math_data[idx]
    }

    fn infer_rose_ast(&mut self, idx: LxRoseAstIdx, ast: &LxRoseAstData) {
        if !self.rose_data.has(idx) {
            let range = self.calc_rose_ast(ast);
            self.rose_data.insert_new(idx, range);
        }
    }

    fn calc_rose_ast(&self, data: &LxRoseAstData) -> LxTokenIdxRange {
        match *data {
            LxRoseAstData::TextEdit { ref buffer } => todo!(),
            LxRoseAstData::Word(token_idx, _) => LxTokenIdxRange::new_single(*token_idx),
            LxRoseAstData::Punctuation(token_idx, _) => LxTokenIdxRange::new_single(*token_idx),
            LxRoseAstData::Math {
                left_dollar_token_idx,
                math_asts,
                right_dollar_token_idx,
            } => LxTokenIdxRange::new_closed(*left_dollar_token_idx, *right_dollar_token_idx),
        }
    }

    fn get_rose_ast_range(&mut self, idx: LxRoseAstIdx) -> LxTokenIdxRange {
        self.infer_rose_ast(idx, &self.ast_arena.rose()[idx]);
        self.rose_data[idx]
    }
}
