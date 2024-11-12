use super::LxEnvironmentPath;

#[derive(Debug, PartialEq, Eq)]
pub struct LxEnvironmentMenu {
    pub align: LxEnvironmentPath,
    pub array: LxEnvironmentPath,
    pub matrix: LxEnvironmentPath,
    pub cases: LxEnvironmentPath,
    pub equation: LxEnvironmentPath,
    pub figure: LxEnvironmentPath,
    pub table: LxEnvironmentPath,
}

impl LxEnvironmentMenu {
    fn new(db: &::salsa::Db) -> Self {
        let p = |s: &str| LxEnvironmentPath::new(s, db);
        Self {
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
pub fn lx_environment_menu(db: &::salsa::Db) -> LxEnvironmentMenu {
    LxEnvironmentMenu::new(db)
}
