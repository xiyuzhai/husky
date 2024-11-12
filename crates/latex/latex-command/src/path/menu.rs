use super::*;

#[derive(Debug, PartialEq, Eq)]
pub struct LxCommandPathMenu {
    pub begin: LxCommandPath,
    pub end: LxCommandPath,
    // maths
    // - letter style
    pub mathbb: LxCommandPath,
    pub mathbf: LxCommandPath,
    pub mathcal: LxCommandPath,
    pub mathit: LxCommandPath,
    pub mathrm: LxCommandPath,
    pub mathsf: LxCommandPath,
    pub mathscr: LxCommandPath,
    // - operators
    // -- relations
    pub r#eq: LxCommandPath,
    pub r#ne: LxCommandPath,
    pub r#in: LxCommandPath,
    pub r#subset: LxCommandPath,
    pub r#supset: LxCommandPath,
    pub r#subseteq: LxCommandPath,
    pub r#supseteq: LxCommandPath,
    pub r#subseteqq: LxCommandPath,
    pub r#supseteqq: LxCommandPath,
    pub r#subsetneq: LxCommandPath,
    pub r#supsetneq: LxCommandPath,
    // -- arithmetic
    pub int: LxCommandPath,
    pub sum: LxCommandPath,
    pub times: LxCommandPath,
    pub otimes: LxCommandPath,
    pub prod: LxCommandPath,
    // - extended letters
    pub alpha: LxCommandPath,
    pub beta: LxCommandPath,
    pub gamma: LxCommandPath,
    pub pi: LxCommandPath,
    // - functions
    pub sin: LxCommandPath,
    pub cos: LxCommandPath,
    // - layouts
    pub sqrt: LxCommandPath,
    pub frac: LxCommandPath,
    // - environments
    pub text: LxCommandPath,
}

impl LxCommandPathMenu {
    fn new(db: &salsa::Db) -> Self {
        let p = |data: &str| LxCommandPath::new_prelude(Coword::from_ref(db, data), db);
        Self {
            begin: p("begin"),
            end: p("end"),
            mathbb: p("mathbb"),
            mathbf: p("mathbf"),
            mathcal: p("mathcal"),
            mathit: p("mathit"),
            mathrm: p("mathrm"),
            mathsf: p("mathsf"),
            mathscr: p("mathscr"),
            // - operators
            // -- relations
            eq: p("eq"),
            ne: p("ne"),
            r#in: p("in"),
            subset: p("subset"),
            supset: p("supset"),
            subseteq: p("subseteq"),
            supseteq: p("supseteq"),
            subseteqq: p("subseteqq"),
            supseteqq: p("supseteqq"),
            subsetneq: p("subsetneq"),
            supsetneq: p("supsetneq"),
            // -- arithmetic
            int: p("int"),
            sum: p("sum"),
            times: p("times"),
            otimes: p("otimes"),
            prod: p("prod"),
            alpha: p("alpha"),
            beta: p("beta"),
            gamma: p("gamma"),
            pi: p("pi"),
            sin: p("sin"),
            cos: p("cos"),
            sqrt: p("sqrt"),
            frac: p("frac"),
            text: p("text"),
        }
    }
}

#[salsa::tracked(return_ref)]
pub fn command_path_menu(db: &salsa::Db) -> LxCommandPathMenu {
    LxCommandPathMenu::new(db)
}
