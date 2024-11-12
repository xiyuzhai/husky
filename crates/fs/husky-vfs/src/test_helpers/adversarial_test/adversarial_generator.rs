use super::*;

pub(super) struct VfsAdversarialGenerator {
    round: u32,
    rng: XRng,
}

impl VfsAdversarialGenerator {
    pub(super) fn from_env() -> Option<Self> {
        let Ok(round) = std::env::var("ADVERSARIAL_ROUND") else {
            return None;
        };
        let round: u32 = round.parse().expect("valid u32");
        Some(Self {
            round,
            rng: XRng::new_time_seeded(),
        })
    }

    pub(super) fn run(
        mut self,
        db: &mut Db,
        module_path: ModulePath,
        f: &impl Fn(&::salsa::Db),
    ) -> Result<(), VfsAdversarial> {
        use indicatif::ProgressBar;

        let bar = ProgressBar::new(self.round as u64);
        for _i in 0..self.round {
            bar.inc(1);
            self.run_step(db, module_path, f)?
        }
        Ok(())
    }

    fn run_step(
        &mut self,
        db: &mut Db,
        module_path: ModulePath,
        f: &impl Fn(&::salsa::Db),
    ) -> Result<(), VfsAdversarial> {
        let text = module_path.raw_text(db);
        let Some(adversarial) = self.generate_adversarial(text) else {
            return Ok(());
        };
        match adversarial.test(db, module_path, f) {
            Ok(_) => Ok(()),
            Err(_) => Err(adversarial),
        }
    }

    fn generate_adversarial(&mut self, text: &str) -> Option<VfsAdversarial> {
        VfsAdversarial::new_rand(text, &mut self.rng)
    }
}
