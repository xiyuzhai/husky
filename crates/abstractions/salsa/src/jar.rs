use std::mem::MaybeUninit;

use enum_index::full_map::EnumFullVecMap;

use super::routes::Routes;

pub trait Jar: std::any::Any + HasJarIndex + Send + Sync + Sized + 'static {
    fn initialize(&mut self, routes: &mut Routes);
}

pub trait JarDyn: std::any::Any + Send + Sync + 'static {
    fn jar_index_dyn(&self) -> JarIndex;
    fn type_name(&self) -> &'static str;
}

impl<'a> dyn JarDyn + 'a {
    fn downcast_ref<Jar: 'static>(&self) -> Option<&Jar> {
        (self as &dyn std::any::Any).downcast_ref()
    }

    fn downcast_mut<Jar: 'static>(&mut self) -> Option<&mut Jar> {
        (self as &mut dyn std::any::Any).downcast_mut()
    }
}

impl<J> JarDyn for J
where
    J: Jar,
{
    fn jar_index_dyn(&self) -> JarIndex {
        J::JAR_INDEX
    }

    fn type_name(&self) -> &'static str {
        std::any::type_name_of_val(self)
    }
}

#[derive(Default)]
pub struct Jars {
    map: EnumFullVecMap<JarIndex, Option<Box<dyn JarDyn>>>,
}

impl Jars {
    pub fn initialize_jar<Jar>(&mut self, routes: &mut Routes)
    where
        Jar: for<'db> crate::jar::Jar + HasJarIndex + Send + Sync + 'static,
    {
        let mut jar_maybe_uninitialized: MaybeUninit<Jar> = MaybeUninit::uninit();
        let jar: &mut Jar = unsafe { std::mem::transmute(&mut jar_maybe_uninitialized) };
        Jar::initialize(jar, routes);
        let index = <Jar as HasJarIndex>::JAR_INDEX;
        debug_assert!(self.map[index].is_none(), "expect `{index:?}` to be empty");
        self.map[index] =
            Some(unsafe { std::mem::transmute::<_, Box<Jar>>(Box::new(jar_maybe_uninitialized)) })
    }

    #[track_caller]
    pub fn jar<Jar>(&self) -> &Jar
    where
        Jar: HasJarIndex + 'static,
    {
        let jar_index = <Jar as HasJarIndex>::JAR_INDEX;
        let Some(jar): Option<&Box<dyn JarDyn>> = self.map[jar_index].as_ref() else {
            unreachable!("{:?} should be initialized", jar_index)
        };
        let jar: &(dyn JarDyn) = &**jar;
        match jar.downcast_ref() {
            Some(jar) => jar,
            None => {
                eprintln!(
                    "jar_index = {:?}, expected = {:?}",
                    jar.jar_index_dyn(),
                    Jar::JAR_INDEX
                );
                eprintln!(
                    "jar.type_id() = {:?}, but expected = {:?}",
                    jar.type_id(),
                    std::any::TypeId::of::<Jar>()
                );
                eprintln!(
                    "jar.type_name() = `{}`, but expected = {:?}",
                    jar.type_name(),
                    std::any::type_name::<Jar>()
                );
                unreachable!(
                    r#"should be the right type.
This could be introduced by a self-reference crate name.

For example, one could have a hack like following in the Cargo.toml file of the `husky-sem-expr` crate,
```
[dev-dependencies]
...
husky-sem-expr = {{ workspace = true, features = ["test_helpers"] }}
```

Then `husky-sem-expr::jar::SemExprJar` and `crate::jar::SemExprJar` have different type ids, for unknown reasons.
"#
                );
            }
        }
    }

    pub fn jar_mut<Jar>(&mut self) -> &mut Jar
    where
        Jar: HasJarIndex + 'static,
    {
        let any: &mut Box<dyn JarDyn> = self.map[<Jar as HasJarIndex>::JAR_INDEX]
            .as_mut()
            .expect("should be initialized");
        let any: &mut (dyn JarDyn) = &mut **any;
        any.downcast_mut().expect("should be the right type")
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, enum_index::IsEnumIndex)]
pub enum JarIndex {
    Jar,
    // comptime
    RustTranspilationJar,
    // devtime
    TraceJar,
    // fs
    CorgiConfigJar,
    ManifestJar,
    ToolchainConfigJar,
    VfsJar,
    // hir
    HirDeclJar,
    HirDefnJar,
    HirEagerExprJar,
    HirExprJar,
    HirLazyExprJar,
    HirPreludeJar,
    HirTypeJar,
    // ide
    CodeLensJar,
    CompletionJar,
    DiagnosticsJar,
    DocumentationJar,
    FoldingRangeJar,
    HoverJar,
    IdeFmtJar,
    InlayHintsJar,
    SemanticTokenJar,
    TokenInfoJar,
    // kernel
    CowordJar,
    DecSignatureJar,
    DecTermJar,
    DecTypeJar,
    EntityPathJar,
    EthSignatureJar,
    EthTermJar,
    FlyTermJar,
    TermPreludeJar,
    PlaceJar,
    // ki
    KiJar,
    KiReprJar,
    // lean
    LnTermJar,
    LnSemExprJar,
    LnHirExprJar,
    // lex
    TextJar,
    TokenJar,
    TokenDataJar,
    TomlTokenJar,
    // linket
    JavelinJar,
    LinketJar,
    // namekian
    NamAstJar,
    // semantics
    SemExprJar,
    SemItemPathDepsJar,
    SemPlaceContractJar,
    SemVarDepsJar,
    SemStaticMutDepsJar,
    // super
    SuperNodeJar,
    // syntax
    AstJar,
    EntityTreeJar,
    ManifestAstJar,
    SynDeclJar,
    SynDefnJar,
    SynExprJar,
    TomlAstJar,
    CorgiConfigAstJar,
    // tex
    LxAstJar,
    LxCommandJar,
    LxEnvironmentJar,
    // visored
    VdZfcTypeJar,
    VdOprJar,
    VdSynExprJar,
    VdSemExprJar,
    VdHirExprJar,
    VdLeanTranspilationJar,
    // vm
    VmirJar,
}

pub trait HasJarIndex {
    const JAR_INDEX: JarIndex;
}
