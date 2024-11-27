#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdEnvironmentPath {
    Document,
    Equation,
    Example,
    Theorem,
    Proof,
}

impl std::fmt::Display for VdEnvironmentPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.lowercase_ident())
    }
}

impl VdEnvironmentPath {
    pub fn lowercase_ident(&self) -> &'static str {
        match self {
            VdEnvironmentPath::Document => "document",
            VdEnvironmentPath::Equation => "equation",
            VdEnvironmentPath::Example => "example",
            VdEnvironmentPath::Theorem => "theorem",
            VdEnvironmentPath::Proof => "proof",
        }
    }

    pub fn pascal_ident(&self) -> &'static str {
        match self {
            VdEnvironmentPath::Document => "Document",
            VdEnvironmentPath::Equation => "Equation",
            VdEnvironmentPath::Example => "Example",
            VdEnvironmentPath::Theorem => "Theorem",
            VdEnvironmentPath::Proof => "Proof",
        }
    }
}
