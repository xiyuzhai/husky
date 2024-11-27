use husky_token::TokenDb;
use husky_token_data::{TokenData, TokenDataError};

use super::*;

#[salsa::tracked(db = DiagnosticsDb, jar = DiagnosticsJar)]
pub struct TokenDiagnosticSheet {
    #[return_ref]
    pub diagnostics: Vec<Diagnostic>,
}

#[salsa::tracked(jar = DiagnosticsJar)]
pub(crate) fn token_diagnostic_sheet(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> TokenDiagnosticSheet {
    let ctx = SheetDiagnosticsContext::new(db, module_path);
    let mut diagnostics = vec![];
    for (range, token) in db.ranged_token_sheet(module_path).ranged_token_iter(db) {
        if let TokenData::Error(e) = token {
            diagnostics.push((range, e).to_diagnostic(&ctx))
        }
    }
    TokenDiagnosticSheet::new(db, diagnostics)
}

impl Diagnose for (&TextPositionRange, &TokenDataError) {
    type Context<'a> = SheetDiagnosticsContext<'a>;

    fn message(&self, _db: &Self::Context<'_>) -> String {
        match self.1 {
            TokenDataError::IncompleteStringLiteralBeforeEof => {
                format!("Syntax Error: incomplete string literal before end of file")
            }
            TokenDataError::IncompleteStringLiteralBeforeEol => {
                format!("Syntax Error: incomplete string literal before end of line")
            }
            TokenDataError::UnexpectedCharAfterBackslash(c) => {
                format!("Syntax Error: unexpected char `{c}` after backslash")
            }
            TokenDataError::UnrecognizedChar(_) => format!("Syntax Error: unrecognized char"),
            TokenDataError::IllFormedLiteral(_) => format!("Syntax Error: ill-formed literal"),
            TokenDataError::NumberPseudoLiteral(_) => format!("Syntax Error: number pseudoliteral"),
            TokenDataError::ParseIntError => format!("Syntax Error: parse int error"),
            TokenDataError::InvalidIntegerSuffix => format!("Syntax Error: invalid integer suffix"),
            TokenDataError::InvalidFloatSuffix => format!("Syntax Error: invalid float suffix"),
            TokenDataError::InvalidIdent => format!("Syntax Error: invalid identifier"),
            TokenDataError::NothingAfterSingleQuote => format!("Syntax Error: nothing after `'`"),
            TokenDataError::InvalidLabel => format!("Syntax Error: invalid label"),
            TokenDataError::NewLineAfterSingleQuote => todo!(),
            TokenDataError::NoNegativeForLiteral(_) => todo!(),
            TokenDataError::RcurlMissingMatchingLcurl => {
                format!("Syntax Error: `{{` missing matching `}}`")
            }
            TokenDataError::ExpectedKeywordAfterAssoc => format!("expected keyword after `assoc`"),
        }
    }

    fn severity(&self) -> DiagnosticSeverity {
        DiagnosticSeverity::Error
    }

    fn range(&self, _ctx: &Self::Context<'_>) -> TextPositionRange {
        // todo: modify for special cases like TokenDataError::IncompleteStringLiteralBeforeEol
        *self.0
    }
}
