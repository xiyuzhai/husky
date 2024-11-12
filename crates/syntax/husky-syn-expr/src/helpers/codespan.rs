pub use codespan_reporting::diagnostic::Severity;
pub use husky_print_utils::eshow;

use super::{
    range::{syn_expr_range_region, SynExprRangeRegion},
    *,
};
use crate::{SynExprIdx, SynExprRegion, SynExprRegionData};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
#[cfg(test)]
use expect_test::expect;
use husky_entity_path::region::RegionPath;
use husky_entity_tree::{
    helpers::tokra_region::HasRegionalTokenIdxBase, region_path::SynNodeRegionPath,
};
use husky_regional_token::RegionalTokenIdxBase;
use husky_text::{HasText, Text};
use husky_text_protocol::offset::TextOffsetRange;
use husky_token::{RangedTokenSheet, TokenDb};
use husky_vfs::path::module_path::ModulePath;
use salsa::DisplayWithDb;

#[macro_export]
macro_rules! emit_note_on_syn_expr_codespan {
    ($syn_expr_region: expr, $db: expr, $($expr_messages: tt),* $(,)?) => {{
        $crate::helpers::codespan::emit_note_on_syn_expr_codespan(
            $syn_expr_region,
            $crate::helpers::codespan::Severity::Note,
            format!("{}:{}:{}", file!(), line!(), column!()),
            $db,
            [$($crate::convert_expr_message!($expr_messages)),*]
        )
    }};
}

#[macro_export]
macro_rules! emit_note_on_syn_pattern_codespan {
    ($syn_expr_region: expr, $db: expr, $($pattern_messages: tt),* $(,)?) => {{
        $crate::helpers::codespan::emit_note_on_syn_pattern_codespan(
            $syn_expr_region,
            $crate::helpers::codespan::Severity::Note,
            format!("{}:{}:{}", file!(), line!(), column!()),
            $db,
            [$($crate::convert_expr_message!($pattern_messages)),*]
        )
    }};
}

#[macro_export]
macro_rules! convert_expr_message {
    (($expr: expr, $message: expr)) => {{
        (
            $expr,
            format!(
                "{}: {}",
                stringify!($expr),
                $crate::helpers::codespan::eshow!($message),
            ),
        )
    }};
    ($expr: expr) => {{
        ($expr, stringify!($expr).to_string())
    }};
}

#[test]
fn convert_expr_message_works() {
    let expr = 1i32;
    let a = 1i32;
    {
        let (expr1, message) = convert_expr_message!(expr);
        assert_eq!(expr, expr1);
        expect!["expr"].assert_eq(&message)
    }
    {
        let (expr1, message) = convert_expr_message!((expr, a));
        assert_eq!(expr, expr1);
        expect!["expr: a = 1"].assert_eq(&message)
    }
    {
        let (expr1, message) = convert_expr_message!((expr, "a"));
    }
}

pub fn emit_note_on_syn_expr_codespan(
    syn_expr_region: SynExprRegion,
    severity: Severity,
    title: impl Into<String>,
    db: &::salsa::Db,
    expr_messages: impl IntoIterator<Item = (SynExprIdx, String)>,
) {
    let mut emitter = SynExprCodespanEmitter::new(syn_expr_region, severity, title, db);
    for (expr, message) in expr_messages {
        emitter.add_expr(expr, message);
    }
    emitter.emit_to_stderr();
}

pub fn emit_note_on_syn_pattern_codespan(
    syn_expr_region: SynExprRegion,
    severity: Severity,
    title: impl Into<String>,
    db: &::salsa::Db,
    pattern_messages: impl IntoIterator<Item = (SynPatternIdx, String)>,
) {
    let mut emitter = SynExprCodespanEmitter::new(syn_expr_region, severity, title, db);
    for (pattern, message) in pattern_messages {
        emitter.add_pattern(pattern, message);
    }
    emitter.emit_to_stderr();
}

struct SynExprCodespanEmitter<'db> {
    db: &'db ::salsa::Db,
    syn_expr_region_data: &'db SynExprRegionData,
    syn_expr_range_region: &'db SynExprRangeRegion,
    ranged_token_sheet: &'db RangedTokenSheet,
    text: Text<'db>,
    region_path: SynNodeRegionPath,
    module_path: ModulePath,
    regional_token_idx_base: RegionalTokenIdxBase,
    files: SimpleFiles<String, &'db str>,
    file_id: usize,
    // ad hoc, just to keep rustc from barking
    diagnostic: Option<Diagnostic<usize>>,
}

/// # constructor
impl<'a> SynExprCodespanEmitter<'a> {
    fn new(
        syn_expr_region: SynExprRegion,
        severity: Severity,
        title: impl Into<String>,
        db: &'a ::salsa::Db,
    ) -> Self {
        let syn_expr_region_data = syn_expr_region.data(db);
        let syn_expr_range_region = syn_expr_range_region(db, syn_expr_region);
        let region_path = syn_expr_region_data.path();
        let module_path = region_path.module_path(db);
        let regional_token_idx_base = region_path.regional_token_idx_base(db).unwrap();
        let ranged_token_sheet = db.ranged_token_sheet(module_path);
        let text = module_path.text(db);
        let mut files = SimpleFiles::new();
        let file_id = files.add(
            module_path
                .abs_path(db)
                .unwrap()
                .to_str()
                .unwrap()
                .to_string(),
            module_path.raw_text(db),
        );
        Self {
            db,
            syn_expr_region_data,
            syn_expr_range_region,
            text,
            ranged_token_sheet,
            region_path,
            module_path,
            regional_token_idx_base,
            files,
            file_id,
            diagnostic: Some(Diagnostic::new(severity).with_message(title)),
        }
    }
}

/// # getters
impl<'a> SynExprCodespanEmitter<'a> {
    fn expr_offset_range(&self, expr: SynExprIdx) -> TextOffsetRange {
        let token_idx_range =
            self.syn_expr_range_region[expr].token_idx_range(self.regional_token_idx_base);
        let text_range = self.ranged_token_sheet.tokens_text_range(token_idx_range);
        self.text.offset_range(text_range)
    }

    fn pattern_offset_range(&self, pattern: SynPatternIdx) -> TextOffsetRange {
        let token_idx_range =
            self.syn_expr_range_region[pattern].token_idx_range(self.regional_token_idx_base);
        let text_range = self.ranged_token_sheet.tokens_text_range(token_idx_range);
        self.text.offset_range(text_range)
    }
}

/// # actions
impl<'a> SynExprCodespanEmitter<'a> {
    fn add_expr(&mut self, expr: SynExprIdx, message: String) {
        let offset_range = self.expr_offset_range(expr);
        self.diagnostic = Some(
            std::mem::take(&mut self.diagnostic)
                .unwrap()
                .with_labels(vec![
                    Label::primary(self.file_id, offset_range).with_message(message)
                ]),
        );
    }

    fn add_pattern(&mut self, pattern: SynPatternIdx, message: String) {
        let offset_range = self.pattern_offset_range(pattern);
        self.diagnostic = Some(
            std::mem::take(&mut self.diagnostic)
                .unwrap()
                .with_labels(vec![
                    Label::primary(self.file_id, offset_range).with_message(message)
                ]),
        );
    }

    fn emit_to_stdout(self) {
        let writer = StandardStream::stdout(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        codespan_reporting::term::emit(
            &mut writer.lock(),
            &config,
            &self.files,
            self.diagnostic.as_ref().unwrap(),
        )
        .unwrap();
    }

    fn emit_to_stderr(self) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        codespan_reporting::term::emit(
            &mut writer.lock(),
            &config,
            &self.files,
            self.diagnostic.as_ref().unwrap(),
        )
        .unwrap();
    }
}
