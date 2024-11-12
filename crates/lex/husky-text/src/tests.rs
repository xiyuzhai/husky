use crate::Text;

#[cfg(test)]
#[track_caller]
pub(crate) fn run_test_on_text(raw_text: &str, f: impl FnOnce(Text)) {
    use husky_text_protocol::line_map::LineMap;

    let line_map = &LineMap::new(raw_text);
    f(Text {
        raw: raw_text,
        line_map,
    });
}

#[test]
fn test_string_length() {
    assert_eq!("a".len(), 1);
    assert_eq!("α".len(), 2);
    assert_eq!("好".len(), 3);
    assert_eq!("→".len(), 3);
    assert_eq!("𒀀".len(), 4);
}
