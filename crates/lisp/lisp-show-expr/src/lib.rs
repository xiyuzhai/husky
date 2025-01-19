pub enum LispShowExpr {
    String(String),
    List(Vec<LispShowExpr>),
}

impl std::fmt::Debug for LispShowExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("LispShowExpr(")?;
        self.show_fmt(f)?;
        f.write_str(")")
    }
}

impl LispShowExpr {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LispShowExpr::String(s) => write!(f, "{}", s),
            LispShowExpr::List(list) => {
                write!(f, "(")?;
                let mut first = true;
                for e in list {
                    if !first {
                        write!(f, " ")?;
                    }
                    e.show_fmt(f)?;
                    first = false;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for LispShowExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_display() {
        let expr = LispShowExpr::String("hello".to_string());
        assert_eq!(expr.to_string(), "hello");
    }

    #[test]
    fn test_empty_list_display() {
        let expr = LispShowExpr::List(vec![]);
        assert_eq!(expr.to_string(), "()");
    }

    #[test]
    fn test_simple_list_display() {
        let expr = LispShowExpr::List(vec![
            LispShowExpr::String("a".to_string()),
            LispShowExpr::String("b".to_string()),
            LispShowExpr::String("c".to_string()),
        ]);
        assert_eq!(expr.to_string(), "(a b c)");
    }

    #[test]
    fn test_nested_list_display() {
        let expr = LispShowExpr::List(vec![
            LispShowExpr::String("define".to_string()),
            LispShowExpr::List(vec![
                LispShowExpr::String("x".to_string()),
                LispShowExpr::String("42".to_string()),
            ]),
        ]);
        assert_eq!(expr.to_string(), "(define (x 42))");
    }
}
