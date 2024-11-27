use super::LxEnvironmentPath;

#[derive(Debug, PartialEq, Eq)]
pub struct LxEnvironmentPathMenu {
    pub document: LxEnvironmentPath,
    // theorems
    pub example: LxEnvironmentPath,
    pub proof: LxEnvironmentPath,
    pub remark: LxEnvironmentPath,
    pub definition: LxEnvironmentPath,
    pub theorem: LxEnvironmentPath,
    pub lemma: LxEnvironmentPath,
    pub corollary: LxEnvironmentPath,
    pub proposition: LxEnvironmentPath,
    // math
    pub align: LxEnvironmentPath,
    pub array: LxEnvironmentPath,
    pub matrix: LxEnvironmentPath,
    pub cases: LxEnvironmentPath,
    pub equation: LxEnvironmentPath,
    pub figure: LxEnvironmentPath,
    pub table: LxEnvironmentPath,
}

impl LxEnvironmentPathMenu {
    fn new() -> Self {
        let p = |s: &str| LxEnvironmentPath::new(s);
        Self {
            document: p("document"),
            example: p("example"),
            proof: p("proof"),
            remark: p("remark"),
            definition: p("definition"),
            theorem: p("theorem"),
            lemma: p("lemma"),
            corollary: p("corollary"),
            proposition: p("proposition"),
            align: p("align"),
            array: p("array"),
            matrix: p("matrix"),
            cases: p("cases"),
            equation: p("equation"),
            figure: p("figure"),
            table: p("table"),
        }
    }
}

lazy_static::lazy_static! {
    pub static ref LX_ENVIRONMENT_PATH_MENU: LxEnvironmentPathMenu = LxEnvironmentPathMenu::new();
}
