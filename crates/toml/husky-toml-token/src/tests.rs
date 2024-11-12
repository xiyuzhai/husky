use super::*;
use expect_test::expect_file;
use husky_coword::jar::CowordJar;

#[salsa::db(CowordJar, husky_vfs::jar::VfsJar, Jar)]
struct DB;

fn err(input: &str, err: TomlTokenError) {
    let db = DB::default();
    let db = &*db;
    let mut t = TomlTokenIter::new(db, input);
    let token = t.next().unwrap().data().clone();
    assert_eq!(token, TomlTokenData::Err(err));
    assert!(t.next().is_none());
}

#[test]
fn literal_strings() {
    fn t(db: &::salsa::Db, input: &str, val: &str, multiline: bool) {
        let mut t = TomlTokenIter::new(db, input);
        let token = t.next().unwrap().data().clone();
        assert_eq!(
            token,
            TomlTokenData::StringLiteral {
                val: Arc::from(val),
                multiline,
            }
        );
        assert!(t.next().is_none());
    }

    let db = DB::default();
    let db = &*db;
    t(db, "''", "", false);
    t(db, "''''''", "", true);
    t(db, "'''\n'''", "", true);
    t(db, "'a'", "a", false);
    t(db, "'\"a'", "\"a", false);
    t(db, "''''a'''", "'a", true);
    t(db, "'''\n'a\n'''", "'a\n", true);
    t(db, "'''a\n'a\r\n'''", "a\n'a\n", true);
}

#[test]
fn basic_strings() {
    fn t(db: &::salsa::Db, input: &str, val: &str, multiline: bool) {
        let mut t = TomlTokenIter::new(db, input);
        let token = t.next().unwrap();
        assert_eq!(
            token.data(),
            &TomlTokenData::StringLiteral {
                val: Arc::from(val),
                multiline,
            }
        );
        assert!(t.next().is_none());
    }

    let db = DB::default();
    let db = &*db;
    t(db, r#""""#, "", false);
    t(db, r#""""""""#, "", true);
    t(db, r#""a""#, "a", false);
    t(db, r#""""a""""#, "a", true);
    t(db, r#""\t""#, "\t", false);
    t(db, r#""\u0000""#, "\0", false);
    t(db, r#""\U00000000""#, "\0", false);
    t(db, r#""\U000A0000""#, "\u{A0000}", false);
    t(db, r#""\\t""#, "\\t", false);
    t(db, "\"\t\"", "\t", false);
    t(db, "\"\"\"\n\t\"\"\"", "\t", true);
    t(db, "\"\"\"\\\n\"\"\"", "", true);
    t(
        db,
        "\"\"\"\\\n     \t   \t  \\\r\n  \t \n  \t \r\n\"\"\"",
        "",
        true,
    );
    t(db, r#""\r""#, "\r", false);
    t(db, r#""\n""#, "\n", false);
    t(db, r#""\b""#, "\u{8}", false);
    t(db, r#""a\fa""#, "a\u{c}a", false);
    t(db, r#""\"a""#, "\"a", false);
    t(db, "\"\"\"\na\"\"\"", "a", true);
    t(db, "\"\"\"\n\"\"\"", "", true);
    t(db, r#""""a\"""b""""#, "a\"\"\"b", true);
    err(r#""\a"#, TomlTokenError::InvalidEscape(2.into(), 'a'));
    err("\"\\\n", TomlTokenError::InvalidEscape(2.into(), '\n'));
    err("\"\\\r\n", TomlTokenError::InvalidEscape(2.into(), '\n'));
    err("\"\\", TomlTokenError::UnterminatedString);
    err(
        "\"\u{0}",
        TomlTokenError::InvalidCharInString(1.into(), '\u{0}'),
    );
    err(r#""\U00""#, TomlTokenError::InvalidHexEscape(5.into(), '"'));
    err(r#""\U00"#, TomlTokenError::UnterminatedString);
    err(
        r#""\uD800"#,
        TomlTokenError::InvalidEscapeValue(2.into(), 0xd800),
    );
    err(
        r#""\UFFFFFFFF"#,
        TomlTokenError::InvalidEscapeValue(2.into(), 0xffff_ffff),
    );
}

#[test]
fn keylike() {
    fn t(db: &::salsa::Db, input: &str) {
        let mut t = TomlTokenIter::new(db, input);
        let token = t.next().unwrap();
        assert_eq!(
            token.data(),
            &TomlTokenData::Word(Coword::from_ref(db, input))
        );
        assert!(t.next().is_none());
    }

    let db = DB::default();
    let db = &*db;
    t(db, "foo");
    t(db, "0bar");
    t(db, "bar0");
    t(db, "1234");
    t(db, "a-b");
    t(db, "a_B");
    t(db, "-_-");
    t(db, "___");
}

#[test]
fn all() {
    fn t(db: &::salsa::Db, input: &str, expected: &[((usize, usize), TomlTokenData, &str)]) {
        let mut tokens = TomlTokenIter::new(db, input);
        let mut actual: Vec<(TomlToken, &str)> = Vec::new();
        while let Some(token) = tokens.next() {
            let code = &input[token.offset_range()];
            actual.push((token, code));
        }
        for (a, b) in actual.iter().zip(expected) {
            assert_eq!(
                (a.0.offset_range().raw_tuple(), a.0.data(), a.1),
                (b.0, &b.1, b.2)
            );
        }
        assert_eq!(actual.len(), expected.len());
    }

    let db = DB::default();
    let db = &*db;
    t(
        db,
        " a ",
        &[((1, 2), TomlTokenData::Word(Coword::from_ref(db, "a")), "a")],
    );

    t(
        db,
        " a\t [[]] \t [] {} , . =\n# foo \r\n#foo \n ",
        &[
            ((1, 2), TomlTokenData::Word(Coword::from_ref(db, "a")), "a"),
            ((4, 5), TomlSpecialToken::LeftBox.into(), "["),
            ((5, 6), TomlSpecialToken::LeftBox.into(), "["),
            ((6, 7), TomlSpecialToken::RightBox.into(), "]"),
            ((7, 8), TomlSpecialToken::RightBox.into(), "]"),
            ((11, 12), TomlSpecialToken::LeftBox.into(), "["),
            ((12, 13), TomlSpecialToken::RightBox.into(), "]"),
            ((14, 15), TomlSpecialToken::LeftCurly.into(), "{"),
            ((15, 16), TomlSpecialToken::RightCurly.into(), "}"),
            ((17, 18), TomlSpecialToken::Comma.into(), ","),
            ((19, 20), TomlSpecialToken::Period.into(), "."),
            ((21, 22), TomlSpecialToken::Equals.into(), "="),
            ((23, 29), TomlTokenData::Comment, "# foo "),
            ((31, 36), TomlTokenData::Comment, "#foo "),
        ],
    );
}

#[test]
fn bare_cr_bad() {
    err("\r", TomlTokenError::UnexpectedChar('\r'));
    err("'\n", TomlTokenError::NewlineInString(1.into()));
    err(
        "'\u{0}",
        TomlTokenError::InvalidCharInString(1.into(), '\u{0}'),
    );
    err("'", TomlTokenError::UnterminatedString);
    err("\u{0}", TomlTokenError::UnexpectedChar('\u{0}'));
}

#[test]
fn bad_comment() {
    let db = DB::default();
    let db = &*db;
    let mut t = TomlTokenIter::new(db, "#\u{0}");
    t.next().unwrap();
    assert_eq!(
        t.next().unwrap().data(),
        &TomlTokenData::Err(TomlTokenError::UnexpectedChar('\u{0}'))
    );
    assert!(t.next().is_none());
}

#[test]
fn builtin_library_toml_token_sheets() {
    use husky_vfs::test_helpers::VfsTestUtilsDb;

    let db = DB::default();
    let db = &*db;
    let _toolchain = db.dev_toolchain().unwrap();
    let path_menu = db.dev_path_menu().unwrap();
    expect_file!["../tests/package_core_toml_token_sheets.txt"].assert_eq(&format!(
        "{:#?}",
        db.toml_token_sheet(path_menu.core_package().manifest_path(db).unwrap().path())
            .as_ref()
            .unwrap()
            .unwrap()
    ));
    expect_file!["../tests/package_std_toml_token_sheets.txt"].assert_eq(&format!(
        "{:#?}",
        db.toml_token_sheet(path_menu.std_package().manifest_path(db).unwrap().path())
            .as_ref()
            .unwrap()
    ));
}
