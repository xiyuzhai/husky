use salsa::DisplayWithDb;

use super::*;

pub(super) struct VfsAdversarialManager {
    module: ModulePath,
    path: PathBuf,
    adversarials: Vec<VfsAdversarial>,
    generator: Option<VfsAdversarialGenerator>,
}

impl VfsAdversarialManager {
    pub(super) fn new(module: ModulePath, path: PathBuf) -> Self {
        let adversarials = match std::fs::read_to_string(&path) {
            Ok(text) => serde_json::from_str(&text).expect("should be deserialized"),
            Err(_) => vec![],
        };
        Self {
            module,
            path,
            adversarials,
            generator: VfsAdversarialGenerator::from_env(),
        }
    }

    pub(super) fn run(mut self, db: &mut Db, f: &impl Fn(&::salsa::Db)) {
        for adversarial in &self.adversarials {
            if adversarial.test(db, self.module, f).is_err() {
                println!(
                    "{}failure against adversial{} `{}{adversarial:?}{}` for module `{}{}{}`",
                    husky_print_utils::RED,
                    husky_print_utils::RESET,
                    husky_print_utils::YELLOW,
                    husky_print_utils::RESET,
                    husky_print_utils::GREEN,
                    self.module.display(db),
                    husky_print_utils::RESET,
                );
                std::process::exit(1)
            }
        }
        if let Some(generator) = self.generator {
            match generator.run(db, self.module, f) {
                Ok(_) => (),
                Err(adversarial) => {
                    self.adversarials.push(adversarial);
                    husky_io_utils::diff_write(
                        &self.path,
                        &serde_json::to_string_pretty(&self.adversarials)
                            .expect("serializing should work"),
                        true,
                    );
                    panic!("found an adversarial")
                }
            }
        }
    }
}
