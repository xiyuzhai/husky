pub mod error;
pub mod expectation;
pub mod inference;
pub mod signature;
pub mod term;

use crate::token::ident::Ident;
use crate::*;

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Type {
    Rec0(TypeRec0),
    Rec1(TypeRec1),
    Rec2(TypeRec2),
    Rec3(TypeRec3),
    Rec4(TypeRec4),
    Rec5(TypeRec5),
    Rec6(TypeRec6),
    Rec7(TypeRec7),
    Rec8(TypeRec8),
    Rec9(TypeRec9),
    Rec10(TypeRec10),
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rec0(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec1(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec2(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec3(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec4(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec5(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec6(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec7(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec8(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec9(slf) => f.write_fmt(format_args!("`{slf:?}`")),
            Self::Rec10(slf) => f.write_fmt(format_args!("`{slf:?}`")),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec0(pub Ident);

impl std::fmt::Debug for TypeRec0 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}", self.0.repr()))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec1 {
    template: TypeTemplate,
    argument: TypeRec0,
}

impl std::fmt::Debug for TypeRec1 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec2 {
    template: TypeTemplate,
    argument: TypeRec1,
}

impl std::fmt::Debug for TypeRec2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec3 {
    template: TypeTemplate,
    argument: TypeRec2,
}

impl std::fmt::Debug for TypeRec3 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec4 {
    template: TypeTemplate,
    argument: TypeRec3,
}

impl std::fmt::Debug for TypeRec4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec5 {
    template: TypeTemplate,
    argument: TypeRec4,
}

impl std::fmt::Debug for TypeRec5 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec6 {
    template: TypeTemplate,
    argument: TypeRec5,
}

impl std::fmt::Debug for TypeRec6 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec7 {
    template: TypeTemplate,
    argument: TypeRec6,
}

impl std::fmt::Debug for TypeRec7 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec8 {
    template: TypeTemplate,
    argument: TypeRec7,
}

impl std::fmt::Debug for TypeRec8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec9 {
    template: TypeTemplate,
    argument: TypeRec8,
}

impl std::fmt::Debug for TypeRec9 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct TypeRec10 {
    template: TypeTemplate,
    argument: TypeRec9,
}

impl std::fmt::Debug for TypeRec10 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.template, self.argument))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeTemplate {
    Option,
    Vec,
}

impl std::fmt::Display for TypeTemplate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeTemplate::Option => f.write_str("Option"),
            TypeTemplate::Vec => f.write_str("Vec"),
        }
    }
}

impl Type {
    pub fn in_option(self) -> Type {
        self.in_template(TypeTemplate::Option)
    }

    pub fn in_vec(self) -> Type {
        self.in_template(TypeTemplate::Vec)
    }

    fn in_template(self, template: TypeTemplate) -> Type {
        match self {
            Type::Rec0(ty) => Type::Rec1(TypeRec1 {
                template,
                argument: ty,
            }),
            Type::Rec1(ty) => Type::Rec2(TypeRec2 {
                template,
                argument: ty,
            }),
            Type::Rec2(ty) => Type::Rec3(TypeRec3 {
                template,
                argument: ty,
            }),
            Type::Rec3(ty) => Type::Rec4(TypeRec4 {
                template,
                argument: ty,
            }),
            Type::Rec4(ty) => Type::Rec5(TypeRec5 {
                template,
                argument: ty,
            }),
            Type::Rec5(ty) => Type::Rec6(TypeRec6 {
                template,
                argument: ty,
            }),
            Type::Rec6(ty) => Type::Rec7(TypeRec7 {
                template,
                argument: ty,
            }),
            Type::Rec7(ty) => Type::Rec8(TypeRec8 {
                template,
                argument: ty,
            }),
            Type::Rec8(ty) => Type::Rec9(TypeRec9 {
                template,
                argument: ty,
            }),
            Type::Rec9(ty) => Type::Rec10(TypeRec10 {
                template,
                argument: ty,
            }),
            Type::Rec10(_) => {
                unreachable!("undefined behavior, exceeding limit!")
            }
        }
    }

    pub fn new_ident(ident: Ident) -> Type {
        Type::Rec0(TypeRec0(ident))
    }
}
