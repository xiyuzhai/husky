use super::*;

#[derive(Debug, PartialEq, Eq)]
pub struct LxCommandPathMenu {
    // - general
    pub begin: LxCommandPath,
    pub end: LxCommandPath,
    // - root
    pub usepackage: LxCommandPath,
    pub documentclass: LxCommandPath,
    pub newtheorem: LxCommandPath,
    // - divisions
    pub part: LxCommandPath,
    pub chapter: LxCommandPath,
    pub section: LxCommandPath,
    pub subsection: LxCommandPath,
    pub subsubsection: LxCommandPath,
    // - maths
    // -- letter style
    pub mathbb: LxCommandPath,
    pub mathbf: LxCommandPath,
    pub mathcal: LxCommandPath,
    pub mathit: LxCommandPath,
    pub mathrm: LxCommandPath,
    pub mathsf: LxCommandPath,
    pub mathscr: LxCommandPath,
    // -- operators
    // --- relations
    pub eq: LxCommandPath,
    pub ne: LxCommandPath,
    pub le: LxCommandPath,
    pub ge: LxCommandPath,
    pub r#in: LxCommandPath,
    pub subset: LxCommandPath,
    pub supset: LxCommandPath,
    pub subseteq: LxCommandPath,
    pub supseteq: LxCommandPath,
    pub subseteqq: LxCommandPath,
    pub supseteqq: LxCommandPath,
    pub subsetneq: LxCommandPath,
    pub supsetneq: LxCommandPath,
    // -- arithmetics
    pub int: LxCommandPath,
    pub sum: LxCommandPath,
    pub times: LxCommandPath,
    pub otimes: LxCommandPath,
    pub prod: LxCommandPath,
    // -- extended letters
    pub alpha: LxCommandPath,
    pub beta: LxCommandPath,
    pub gamma: LxCommandPath,
    pub pi: LxCommandPath,
    // --- functions
    pub sin: LxCommandPath,
    pub cos: LxCommandPath,
    // -- layouts
    pub sqrt: LxCommandPath,
    pub frac: LxCommandPath,
    // -- environments
    pub text: LxCommandPath,
}

impl LxCommandPathMenu {
    fn new(db: &salsa::Db) -> Self {
        let p = |data: &str| LxCommandPath::new_prelude(Coword::from_ref(db, data), db);
        Self {
            // - general
            begin: p("begin"),
            end: p("end"),
            // - root
            usepackage: p("usepackage"),
            documentclass: p("documentclass"),
            newtheorem: p("newtheorem"),
            // - divisions
            part: p("part"),
            chapter: p("chapter"),
            section: p("section"),
            subsection: p("subsection"),
            subsubsection: p("subsubsection"),
            // - maths
            // ## letter style
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
            le: p("le"),
            ge: p("ge"),
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
            // -- extended letters
            alpha: p("alpha"),
            beta: p("beta"),
            gamma: p("gamma"),
            pi: p("pi"),
            // -- functions
            sin: p("sin"),
            cos: p("cos"),
            // -- layouts
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
