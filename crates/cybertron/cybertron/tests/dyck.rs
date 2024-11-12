use cybertron::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Delimiter(u8);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PreAst {
    LeftDelimiter(Delimiter),
    RightDelimiter(Delimiter),
}

fn dyck_lang(mut pre_asts: Seq<Option<PreAst>>, n: usize) -> Seq<Option<PreAst>> {
    for _ in 0..n {
        pre_asts = dyck_lang_step(pre_asts)
    }
    pre_asts
}

fn dyck_lang_step(pre_asts: Seq<Option<PreAst>>) -> Seq<Option<PreAst>> {
    let pre_asts_nearest_left = pre_asts.nearest_left();
    let pre_asts_nearest_right = pre_asts.nearest_right();
    dyck_lang_step_aux.apply(pre_asts_nearest_left, pre_asts, pre_asts_nearest_right)
}

fn dyck_lang_step_aux(
    pre_ast_nearest_left: Option<(Idx, PreAst)>,
    pre_ast: Option<PreAst>,
    pre_ast_nearest_right: Option<(Idx, PreAst)>,
) -> Option<PreAst> {
    match pre_ast? {
        PreAst::LeftDelimiter(delimiter) => match pre_ast_nearest_right {
            Some((_, PreAst::RightDelimiter(delimiter1))) if delimiter1 == delimiter => None,
            _ => pre_ast,
        },
        PreAst::RightDelimiter(delimiter) => match pre_ast_nearest_left {
            Some((_, PreAst::LeftDelimiter(delimiter1))) if delimiter1 == delimiter => None,
            _ => pre_ast,
        },
    }
}

impl PreAst {
    fn from_char(c: char) -> Self {
        match c {
            '(' => PreAst::LeftDelimiter(Delimiter(0)),
            ')' => PreAst::RightDelimiter(Delimiter(0)),
            '[' => PreAst::LeftDelimiter(Delimiter(1)),
            ']' => PreAst::RightDelimiter(Delimiter(1)),
            '{' => PreAst::LeftDelimiter(Delimiter(2)),
            '}' => PreAst::RightDelimiter(Delimiter(2)),
            _ => panic!(),
        }
    }
}

#[test]
fn dyck_lang_works() {
    fn t(input: &str) {
        use husky_print_utils::p;

        let pre_asts = Seq::new(input.chars().map(|c| Some(PreAst::from_char(c))).collect());
        let pre_asts = dyck_lang(pre_asts, 10);
        for pre_ast in pre_asts.data() {
            assert!(pre_ast.is_none());
        }
    }
    t("");
    t("[]");
    t("[][]");
    t("[[][]]");
    t("[[()][]]");
}
