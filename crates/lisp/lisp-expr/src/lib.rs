pub enum LispExpr {
    String(String),
    List(Vec<LispExpr>),
}

impl LispExpr {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LispExpr::String(s) => write!(f, "{}", s),
            LispExpr::List(list) => {
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

impl std::fmt::Display for LispExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_display() {
        let expr = LispExpr::String("hello".to_string());
        assert_eq!(expr.to_string(), "hello");
    }

    #[test]
    fn test_empty_list_display() {
        let expr = LispExpr::List(vec![]);
        assert_eq!(expr.to_string(), "()");
    }

    #[test]
    fn test_simple_list_display() {
        let expr = LispExpr::List(vec![
            LispExpr::String("a".to_string()),
            LispExpr::String("b".to_string()),
            LispExpr::String("c".to_string()),
        ]);
        assert_eq!(expr.to_string(), "(a b c)");
    }

    #[test]
    fn test_nested_list_display() {
        let expr = LispExpr::List(vec![
            LispExpr::String("define".to_string()),
            LispExpr::List(vec![
                LispExpr::String("x".to_string()),
                LispExpr::String("42".to_string()),
            ]),
        ]);
        assert_eq!(expr.to_string(), "(define (x 42))");
    }
}
