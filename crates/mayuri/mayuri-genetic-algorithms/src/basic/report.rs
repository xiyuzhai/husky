use std::fmt;

#[derive(Default, Debug)]
pub struct Report {
    pub generations: Vec<GenerationReport>,
}

#[derive(Clone)]
pub struct GenerationReport {
    pub generation: usize,
    pub best_fitness: i32,
    pub best_genome: Vec<bool>,
    pub population_size: usize,
}

impl fmt::Debug for GenerationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let genome_str: String = self
            .best_genome
            .iter()
            .map(|&b| if b { '1' } else { '0' })
            .collect();
        f.debug_struct("GenerationReport")
            .field("generation", &self.generation)
            .field("best_fitness", &self.best_fitness)
            .field("best_genome", &genome_str)
            .field("population_size", &self.population_size)
            .finish()
    }
}
