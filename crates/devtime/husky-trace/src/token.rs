use crate::{registry::assoc_trace::IsAssocTraceRegistry, *};

use husky_text::{HasText, Text};
use husky_token::{RangedTokenSheet, TokenDb, TokenIdx, TokenIdxRange};
use husky_token_info::{TokenInfoDb, TokenInfoSheetRef};
use husky_trace_protocol::view::{TraceViewLineData, TraceViewTokenData};
use husky_vfs::path::module_path::ModulePath;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TraceViewLines {
    data: Vec<TraceViewLineData>,
}

impl TraceViewLines {
    pub fn data(self) -> Vec<TraceViewLineData> {
        self.data
    }

    pub(crate) fn new<AssocTraceRegistry>(
        module_path: ModulePath,
        token_idx_range: TokenIdxRange,
        registry: AssocTraceRegistry,
        db: &::salsa::Db,
    ) -> Self
    where
        AssocTraceRegistry: IsAssocTraceRegistry,
    {
        let mut builder = TraceViewTokensBuilder::new(db, module_path, registry);
        builder.generate_tokens(token_idx_range);
        builder.finish()
    }
}

struct TraceViewTokensBuilder<'a, AssocTraceRegistry>
where
    AssocTraceRegistry: IsAssocTraceRegistry,
{
    db: &'a ::salsa::Db,
    text: Text<'a>,
    ranged_token_sheet: &'a RangedTokenSheet,
    token_info_sheet: TokenInfoSheetRef<'a>,
    lines_data: Vec<TraceViewLineData>,
    tokens_data: Vec<TraceViewTokenData>,
    assoc_trace_registry: AssocTraceRegistry,
}

impl<'a, AssocTraceRegistry> TraceViewTokensBuilder<'a, AssocTraceRegistry>
where
    AssocTraceRegistry: IsAssocTraceRegistry,
{
    fn new(
        db: &'a ::salsa::Db,
        module_path: ModulePath,
        assoc_trace_registry: AssocTraceRegistry,
    ) -> Self {
        // db.text
        Self {
            db,
            ranged_token_sheet: db.ranged_token_sheet(module_path),
            token_info_sheet: db.token_info_sheet_ref(module_path).unwrap(),
            text: module_path.text(db),
            lines_data: vec![],
            tokens_data: vec![],
            assoc_trace_registry,
        }
    }

    fn generate_tokens(&mut self, token_idx_range: TokenIdxRange) {
        for token_idx in token_idx_range {
            self.generate_token(token_idx)
        }
    }

    fn generate_token(&mut self, token_idx: TokenIdx) {
        let text_range = self.ranged_token_sheet.token_text_range(token_idx);
        let text = self.text.text_within(text_range);
        let db = self.db;
        let (token_class, src) = match self.token_info_sheet[token_idx].last() {
            Some(token_info) => (token_info.data().token_class(db), Some(token_info.source())),
            None => (
                self.ranged_token_sheet.token_sheet_data(db)[token_idx].default_token_class(),
                None,
            ),
        };
        let assoc_trace_id = src
            .map(|src| {
                self.assoc_trace_registry
                    .get_or_issue_assoc_trace_id(src, db)
            })
            .flatten();
        // todo: handle inline comments
        let spaces_before: u32 = if token_idx.index() > 0 {
            let prev_text_range = self.ranged_token_sheet.token_text_range(token_idx - 1);
            if prev_text_range.start.line == text_range.end.line {
                text_range.start.col.index32() - prev_text_range.end.col.index32()
            } else {
                self.new_line_if_tokens_data_is_empty();
                text_range.start.col.index32()
            }
        } else {
            text_range.start.col.index32()
        };
        self.tokens_data.push(TraceViewTokenData::new(
            text.to_string(),
            token_class,
            spaces_before,
            assoc_trace_id.map(Into::into),
        ));
    }

    fn new_line_if_tokens_data_is_empty(&mut self) {
        if !self.tokens_data.is_empty() {
            self.lines_data.push(TraceViewLineData::new(std::mem::take(
                &mut self.tokens_data,
            )))
        }
    }

    fn finish(mut self) -> TraceViewLines {
        assert!(self.tokens_data.len() > 0);
        self.lines_data
            .push(TraceViewLineData::new(self.tokens_data));
        TraceViewLines {
            data: self.lines_data,
        }
    }
}
