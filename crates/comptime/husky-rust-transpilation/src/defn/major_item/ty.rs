use super::*;

use husky_hir_decl::{PropsFieldHirDecl, TupleFieldHirDecl};

impl TranspileToRust for TypeHirDefn {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        match self {
            TypeHirDefn::Enum(hir_defn) => hir_defn.transpile_to_rust(builder),
            TypeHirDefn::PropsStruct(hir_defn) => hir_defn.transpile_to_rust(builder),
            TypeHirDefn::TupleStruct(hir_defn) => hir_defn.transpile_to_rust(builder),
            TypeHirDefn::UnitStruct(_) => todo!(),
            TypeHirDefn::Extern(_) =>
            /* ad hoc */
            {
                ()
            }
            TypeHirDefn::Union(_) => todo!(),
        }
    }
}

impl TranspileToRust for EnumTypeHirDefn {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let hir_decl = self.hir_decl(db);
        builder.keyword(RustKeyword::Struct);
        hir_decl.path(db).ident(db).transpile_to_rust(builder);
        hir_decl.template_parameters(db).transpile_to_rust(builder);
        // builder.bracketed_comma_list(RustBracket::Curl, hir_decl.variants(db))
    }
}

impl TranspileToRust for PropsStructTypeHirDefn {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let hir_decl = self.hir_decl(db);
        builder.keyword(RustKeyword::Struct);
        hir_decl.path(db).ident(db).transpile_to_rust(builder);
        hir_decl.template_parameters(db).transpile_to_rust(builder);
        builder.bracketed_comma_list(RustBracket::Curl, hir_decl.fields(db))
    }
}

impl TranspileToRust for PropsFieldHirDecl {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        self.ident().transpile_to_rust(builder);
        builder.punctuation(RustPunctuation::Colon);
        self.ty().transpile_to_rust(builder)
    }
}

impl TranspileToRust for TupleStructTypeHirDefn {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        let db = builder.db();
        let hir_decl = self.hir_decl(db);
        builder.keyword(RustKeyword::Struct);
        hir_decl.path(db).ident(db).transpile_to_rust(builder);
        hir_decl.template_parameters(db).transpile_to_rust(builder);
        builder.bracketed_comma_list(RustBracket::Curl, hir_decl.fields(db))
    }
}

impl TranspileToRust for TupleFieldHirDecl {
    fn transpile_to_rust(&self, builder: &mut RustTranspilationBuilder) {
        self.ty().transpile_to_rust(builder)
    }
}