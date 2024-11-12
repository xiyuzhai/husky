use super::*;
use husky_entity_path::path::major_item::ty::PreludeTypePath;

impl salsa::DisplayWithDb for AbstractVariableIndex {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &salsa::Db,
    ) -> std::fmt::Result {
        match self.ty_family {
            DecTermFamily::Category(cat) if cat == Sort::PROP => match self.disambiguator {
                0 => f.write_str("p"),
                1 => f.write_str("q"),
                idx => f.write_fmt(format_args!("p{}", idx)),
            },
            DecTermFamily::Category(cat) if cat == Sort::TYPE => match self.disambiguator {
                0 => f.write_str("t"),
                1 => f.write_str("s"),
                idx => f.write_fmt(format_args!("t{}", idx)),
            },
            DecTermFamily::Category(_cat) => match self.disambiguator {
                0 => f.write_str("α"),
                1 => f.write_str("β"),
                2 => f.write_str("γ"),
                3 => f.write_str("δ"),
                4 => f.write_str("ϵ"),
                5 => f.write_str("ζ"),
                6 => f.write_str("η"),
                idx => f.write_fmt(format_args!("α{}", idx)),
            },
            DecTermFamily::TypePath(path)
                if path.prelude(db) == Some(PreludeTypePath::LIFETIME) =>
            {
                match self.disambiguator {
                    0 => f.write_str("'a"),
                    1 => f.write_str("'b"),
                    2 => f.write_str("'c"),
                    3 => f.write_str("'d"),
                    4 => f.write_str("'e"),
                    5 => f.write_str("'f"),
                    idx => f.write_fmt(format_args!("'a{}", idx)),
                }
            }
            DecTermFamily::TypePath(path) if path.prelude(db) == Some(PreludeTypePath::PLACE) => {
                match self.disambiguator {
                    0 => f.write_str("'α"),
                    1 => f.write_str("'β"),
                    2 => f.write_str("'γ"),
                    3 => f.write_str("'δ"),
                    4 => f.write_str("'ϵ"),
                    5 => f.write_str("'ζ"),
                    6 => f.write_str("'η"),
                    idx => f.write_fmt(format_args!("'α{}", idx)),
                }
            }
            DecTermFamily::TypePath(_) | DecTermFamily::Other => match self.disambiguator {
                0 => f.write_str("a"),
                1 => f.write_str("b"),
                idx => f.write_fmt(format_args!("a{}", idx)),
            },
        }
    }
}
