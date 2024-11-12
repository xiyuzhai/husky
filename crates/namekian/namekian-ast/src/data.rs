pub mod division;
pub mod entry;

use self::paragraph::NamParagraphLead;
use crate::{data::division::NamDivisionKind, parser::NamParser, region::NamAstRegion, *};
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum NamAstData {
    Division {
        kind: NamDivisionKind,
        items: NamAstIdxRange,
    },
    Entry(NamAstRegion),
}

pub type NamAstArena = Arena<NamAstData>;
pub type NamAstIdx = ArenaIdx<NamAstData>;
pub type NamAstIdxRange = ArenaIdxRange<NamAstData>;

impl<'a> NamParser<'a> {
    pub(crate) fn parse_asts(&mut self) -> NamAstIdxRange {
        let mut asts: Vec<NamAstData> = vec![];
        while let Some(ast) = self.parse_ast() {
            asts.push(ast)
        }
        self.alloc_asts(asts)
    }

    fn parse_ast(&mut self) -> Option<NamAstData> {
        let paragraph = self.next_paragraph_within_current_level()?;
        Some(match paragraph.lead {
            NamParagraphLead::Chapter => {
                self.parse_division_ast(NamDivisionKind::Chapter, paragraph)
            }
            NamParagraphLead::Section => {
                self.parse_division_ast(NamDivisionKind::Section, paragraph)
            }
            NamParagraphLead::Subsection => {
                self.parse_division_ast(NamDivisionKind::Subsection, paragraph)
            }
            NamParagraphLead::Subsubsection => {
                self.parse_division_ast(NamDivisionKind::Subsubsection, paragraph)
            }
            NamParagraphLead::Notion => todo!(),
            NamParagraphLead::Semantics => todo!(),
            NamParagraphLead::Proposition => todo!(),
            NamParagraphLead::Theorem => todo!(),
            NamParagraphLead::HeavyArrow => todo!(),
            NamParagraphLead::Other => todo!(),
        })
    }
}

#[test]
fn nam_ast_parsing_expects() {
    fn t(input: &str, expected: &Expect) {
        let mut parser = NamParser::new(input);
        let root_asts = parser.parse_asts();
        let arena = parser.finish();
        expected.assert_debug_eq(&(root_asts, arena))
    }
    t(
        "",
        &expect![[r#"
        (
            ArenaIdxRange(
                0..0,
            ),
            Arena {
                data: [],
            },
        )
    "#]],
    );
    t(
        "chapter",
        &expect![[r#"
            (
                ArenaIdxRange(
                    0..1,
                ),
                Arena {
                    data: [
                        Division {
                            kind: Chapter,
                            items: ArenaIdxRange(
                                0..0,
                            ),
                        },
                    ],
                },
            )
        "#]],
    );
    t(
        "chapter\n\nsection",
        &expect![[r#"
            (
                ArenaIdxRange(
                    1..2,
                ),
                Arena {
                    data: [
                        Division {
                            kind: Section,
                            items: ArenaIdxRange(
                                0..0,
                            ),
                        },
                        Division {
                            kind: Chapter,
                            items: ArenaIdxRange(
                                0..1,
                            ),
                        },
                    ],
                },
            )
        "#]],
    );
}
