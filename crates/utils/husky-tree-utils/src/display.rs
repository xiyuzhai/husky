use char_set::CharSet;

pub mod char_set;

pub struct DisplayTree {
    value: String,
    children: Vec<DisplayTree>,
}

impl DisplayTree {
    pub fn new(value: String, children: Vec<DisplayTree>) -> Self {
        Self { value, children }
    }

    pub fn show(&self, chars: &CharSet) -> String {
        let mut builder = String::new();
        self.build_string("", "", &mut builder, &chars);
        builder
    }

    fn build_string(
        &self,
        prefix: &str,
        child_prefix: &str,
        builder: &mut String,
        chars: &CharSet,
    ) {
        // Add current node
        builder.push_str(&format!("{}{}\n", prefix, self.value));

        // Process children
        Self::process_trees(&self.children, child_prefix, builder, chars);
    }

    fn process_trees(
        children: &[DisplayTree],
        child_prefix: &str,
        builder: &mut String,
        chars: &CharSet,
    ) {
        if !children.is_empty() {
            for (i, child) in children.iter().enumerate() {
                let is_last = i == children.len() - 1;
                let (next_prefix, next_child_prefix) = if is_last {
                    (
                        format!("{}{}─ ", child_prefix, chars.end_connector),
                        format!("{}  ", child_prefix),
                    )
                } else {
                    (
                        format!("{}{}─ ", child_prefix, chars.connector),
                        format!("{}{} ", child_prefix, chars.vertical),
                    )
                };
                child.build_string(&next_prefix, &next_child_prefix, builder, chars);
            }
        }
    }

    pub fn show_trees(trees: &[DisplayTree], chars: &CharSet) -> String {
        let mut builder = String::new();
        Self::process_trees(trees, "", &mut builder, chars);
        builder
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn test_single_node() {
        let tree = DisplayTree::new("root".to_string(), vec![]);
        expect![[r#"
            root
        "#]]
        .assert_eq(&tree.show(&CharSet::default()));
    }

    #[test]
    fn test_single_child() {
        let tree = DisplayTree::new(
            "root".to_string(),
            vec![DisplayTree::new("child".to_string(), vec![])],
        );
        let expected = "\
root
└─ child
";
        expect![[r#"
            root
            └─ child
        "#]]
        .assert_eq(&tree.show(&CharSet::default()));
    }

    #[test]
    fn test_multiple_children() {
        let tree = DisplayTree::new(
            "root".to_string(),
            vec![
                DisplayTree::new("child1".to_string(), vec![]),
                DisplayTree::new("child2".to_string(), vec![]),
            ],
        );
        expect![[r#"
            root
            ├─ child1
            └─ child2
        "#]]
        .assert_eq(&tree.show(&CharSet::default()));
    }

    #[test]
    fn test_nested_children() {
        let tree = DisplayTree::new(
            "root".to_string(),
            vec![
                DisplayTree::new(
                    "child1".to_string(),
                    vec![DisplayTree::new("grandchild".to_string(), vec![])],
                ),
                DisplayTree::new("child2".to_string(), vec![]),
            ],
        );
        expect![[r#"
            root
            ├─ child1
            │ └─ grandchild
            └─ child2
        "#]]
        .assert_eq(&tree.show(&CharSet::default()));
    }

    #[test]
    fn test_complex_tree() {
        let tree = DisplayTree::new(
            "+".to_string(),
            vec![
                DisplayTree::new(
                    "-".to_string(),
                    vec![DisplayTree::new(
                        "Int".to_string(),
                        vec![DisplayTree::new("2".to_string(), vec![])],
                    )],
                ),
                DisplayTree::new(
                    "Int".to_string(),
                    vec![DisplayTree::new("7".to_string(), vec![])],
                ),
            ],
        );
        expect![[r#"
            +
            ├─ -
            │ └─ Int
            │   └─ 2
            └─ Int
              └─ 7
        "#]]
        .assert_eq(&tree.show(&CharSet::default()));
    }
}
