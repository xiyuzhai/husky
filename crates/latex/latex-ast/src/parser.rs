use crate::{
    ast::{
        lisp::{LxLispAstData, LxLispAstIdxRange},
        math::{LxMathAstData, LxMathAstIdx, LxMathAstIdxRange},
        root::{LxRootAstData, LxRootAstIdxRange},
        rose::{LxRoseAstData, LxRoseAstIdx, LxRoseAstIdxRange},
        LxAstArena, LxAstData, LxAstIdx, LxAstIdxRange,
    },
    region::LxAstRegionData,
};
use latex_command::{
    path::menu::{LxCommandPathMenu, LX_COMMAND_PATH_MENU},
    signature::table::LxCommandSignatureTable,
};
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_prelude::mode::LxMode;
use latex_token::{
    idx::{
        LxLispTokenIdx, LxMathTokenIdx, LxNameTokenIdx, LxRootTokenIdx, LxRoseTokenIdx,
        LxSpecTokenIdx,
    },
    lane::LxTokenLane,
    lexer::LxLexer,
    storage::LxTokenStorage,
    token::{
        lisp::LxLispTokenData, math::LxMathTokenData, name::LxNameTokenData, root::LxRootTokenData,
        rose::LxRoseTokenData, spec::LxSpecTokenData,
    },
};
use std::{borrow::BorrowMut, iter::Peekable};

pub(crate) struct LxAstParser<'a> {
    command_path_menu: &'a LxCommandPathMenu,
    command_signature_table: &'a LxCommandSignatureTable,
    environment_signature_table: &'a LxEnvironmentSignatureTable,
    lexer: LxLexer<'a>,
    mode: LxMode,
    arena: &'a mut LxAstArena,
}

/// # constructor
impl<'a> LxAstParser<'a> {
    pub(crate) fn new(
        command_signature_table: &'a LxCommandSignatureTable,
        environment_signature_table: &'a LxEnvironmentSignatureTable,
        input: &'a str,
        lane: LxTokenLane,
        mode: LxMode,
        token_storage: &'a mut LxTokenStorage,
        arena: &'a mut LxAstArena,
    ) -> Self {
        let command_path_menu = &LX_COMMAND_PATH_MENU;
        Self {
            command_path_menu,
            command_signature_table,
            environment_signature_table,
            lexer: LxLexer::new(input, lane, token_storage),
            mode,
            arena,
        }
    }
}

impl<'a> LxAstParser<'a> {
    pub(crate) fn mode(&self) -> LxMode {
        self.mode
    }

    pub(crate) fn command_path_menu(&self) -> &'a LxCommandPathMenu {
        self.command_path_menu
    }

    pub(crate) fn command_signature_table(&self) -> &'a LxCommandSignatureTable {
        self.command_signature_table
    }

    pub(crate) fn environment_signature_table(&self) -> &'a LxEnvironmentSignatureTable {
        self.environment_signature_table
    }

    pub(crate) fn arena(&self) -> &LxAstArena {
        self.arena
    }
}

/// # actions
impl<'a> LxAstParser<'a> {
    pub(crate) fn alloc_math_asts(&mut self, asts: Vec<LxMathAstData>) -> LxMathAstIdxRange {
        self.arena.math.alloc_batch(asts)
    }

    pub(crate) fn alloc_math_ast(&mut self, ast: LxMathAstData) -> LxMathAstIdx {
        self.arena.math.alloc_one(ast)
    }

    pub(crate) fn alloc_rose_ast(&mut self, ast: LxRoseAstData) -> LxRoseAstIdx {
        self.arena.rose.alloc_one(ast)
    }

    pub(crate) fn alloc_rose_asts(&mut self, asts: Vec<LxRoseAstData>) -> LxRoseAstIdxRange {
        self.arena.rose.alloc_batch(asts)
    }

    pub(crate) fn alloc_lisp_asts(&mut self, asts: Vec<LxLispAstData>) -> LxLispAstIdxRange {
        self.arena.lisp.alloc_batch(asts)
    }

    pub(crate) fn alloc_root_asts(&mut self, asts: Vec<LxRootAstData>) -> LxRootAstIdxRange {
        self.arena.root.alloc_batch(asts)
    }

    pub(crate) fn next_lisp_token(&mut self) -> Option<(LxLispTokenIdx, LxLispTokenData)> {
        self.lexer.next_lisp_token()
    }

    pub(crate) fn peek_lisp_token_data(&mut self) -> Option<LxLispTokenData> {
        self.lexer.peek_lisp_token_data()
    }

    pub(crate) fn peek_math_token_data(&mut self) -> Option<LxMathTokenData> {
        self.lexer.peek_math_token_data()
    }

    pub(crate) fn peek_rose_token_data(&mut self) -> Option<LxRoseTokenData> {
        self.lexer.peek_rose_token_data()
    }

    pub(crate) fn next_math_token(&mut self) -> Option<(LxMathTokenIdx, LxMathTokenData)> {
        self.lexer.next_math_token()
    }

    pub(crate) fn next_root_token(&mut self) -> Option<(LxRootTokenIdx, LxRootTokenData)> {
        self.lexer.next_root_token()
    }

    pub(crate) fn peek_root_token_data(&mut self) -> Option<LxRootTokenData> {
        self.lexer.peek_root_token_data()
    }

    pub(crate) fn next_rose_token(&mut self) -> Option<(LxRoseTokenIdx, LxRoseTokenData)> {
        self.lexer.next_rose_token()
    }

    pub(crate) fn next_name_token(&mut self) -> Option<(LxNameTokenIdx, LxNameTokenData)> {
        self.lexer.next_name_token()
    }

    pub(crate) fn next_spec_token(&mut self) -> Option<(LxSpecTokenIdx, LxSpecTokenData)> {
        self.lexer.next_spec_token()
    }
}
