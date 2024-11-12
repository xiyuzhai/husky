// use crate::routes::Routes;
// use crate::*;
// use enum_index::full_map::EnumFullVecMap;
// use husky_salsa_log_utils::HasLogger;
// use std::mem::MaybeUninit;

// pub struct Db {
//     storage: crate::Storage,
// }

// impl Db {
//     /// here we use fn instead of impl FnOnce to save compilation time
//     pub fn new(initialize_jars: fn(&mut Jars, &mut Routes)) -> Self {
//         Self {
//             storage: crate::Storage::new(initialize_jars),
//         }
//     }
// }

// impl HasLogger for Db {
//     fn logger(&self) -> &husky_salsa_log_utils::Logger {
//         todo!()
//     }
// }

// #[derive(Default)]
// pub struct TestJars {
//     map: EnumFullVecMap<JarIndex, Option<Box<dyn std::any::Any + Sync + Send>>>,
// }

// impl TestJars {
//     pub fn initialize_jar<Jar>(&mut self, routes: &mut Routes)
//     where
//         Jar: for<'db> crate::jar::Jar + HasJarIndex + Send + Sync + 'static,
//     {
//         let mut jar_maybe_uninitialized: MaybeUninit<Jar> = MaybeUninit::uninit();
//         let jar: &mut Jar = unsafe { std::mem::transmute(&mut jar_maybe_uninitialized) };
//         Jar::initialize(jar, routes);
//         let index = <Jar as HasJarIndex>::JAR_INDEX;
//         debug_assert!(self.map[index].is_none());
//         self.map[index] =
//             Some(unsafe { std::mem::transmute::<_, Box<Jar>>(Box::new(jar_maybe_uninitialized)) })
//     }
// }
