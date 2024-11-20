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
    fn new(db: &::salsa::Db) -> Self {
        let p = |s: &str| LxEnvironmentPath::new(s, db);
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

#[salsa::tracked(return_ref)]
pub fn lx_environment_path_menu(db: &::salsa::Db) -> LxEnvironmentPathMenu {
    LxEnvironmentPathMenu::new(db)
}
