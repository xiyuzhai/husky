use crate::{char::TextCharIter, span::TextSpan};

pub struct Paragraph<'a> {
    pub content: &'a str,
    pub span: TextSpan,
}

pub struct ParagraphIter<'a> {
    chars: TextCharIter<'a>,
}

impl<'a> ParagraphIter<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: TextCharIter::new(input),
        }
    }
}

impl<'a> std::iter::Iterator for ParagraphIter<'a> {
    type Item = Paragraph<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.chars.current_offset();
        let mut prev_nonspace_char_is_newline = false;
        self.chars.eat_chars_while(|c| c == '\n');
        let content = self.chars.next_str_slice_while(|c| {
            if c == '\n' {
                if prev_nonspace_char_is_newline {
                    false
                } else {
                    prev_nonspace_char_is_newline = true;
                    true
                }
            } else {
                if c != ' ' {
                    prev_nonspace_char_is_newline = false;
                }
                true
            }
        });
        let end = self.chars.current_offset();
        // if the content is all white spaces or new lines, ignore it
        if !content.is_empty() && content.chars().all(|c| c == ' ' || c == '\n') {
            return self.next();
        }
        (!content.is_empty()).then_some(Paragraph {
            content: content.trim_end_matches('\n'),
            span: TextSpan {
                start: start.index(),
                end: end.index(),
            },
        })
    }
}

#[test]
fn paragraph_iter_works() {
    #[track_caller]
    fn t(input: &str, expected: &[&str]) {
        let paragraphs: Vec<_> = ParagraphIter::new(input).collect();
        assert_eq!(paragraphs.len(), expected.len());
        for (paragraph, &expected) in paragraphs.iter().zip(expected) {
            assert_eq!(paragraph.content, expected);
        }
    }

    t("", &[]);
    t(
        r#"
"#,
        &[],
    );
    t(
        r#"

"#,
        &[],
    );
    t(
        r#"

"#,
        &[],
    );
    t(
        r#"
   
"#,
        &[],
    );
    t(
        r#"
aaa
"#,
        &["aaa"],
    );
    t(
        r#"
  aaa
"#,
        &["  aaa"],
    );
    t(
        r#"
  aaa
  bbb
"#,
        &["  aaa\n  bbb"],
    );
    t(
        r#"
  aaa

bbb
"#,
        &["  aaa", "bbb"],
    );
    t(
        r#"
  aaa

   bbb
"#,
        &["  aaa", "   bbb"],
    );
}
