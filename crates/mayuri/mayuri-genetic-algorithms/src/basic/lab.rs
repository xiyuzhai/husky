use super::individual::Individual;
use super::report::{GenerationReport, Report};
use super::*;

pub struct Lab {
    population_size: usize,
    num_genes: usize,
    mutation_rate: f64,
    max_generations: usize,
    target: Vec<bool>,
    population: Vec<Individual>,
    max_population_size: usize,
    rng: ChaCha8Rng,
    pub report: Report,
}

impl Lab {
    pub fn new(
        population_size: usize,
        num_genes: usize,
        mutation_rate: f64,
        max_generations: usize,
        target: Vec<bool>,
        seed: u64,
    ) -> Self {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let population = (0..population_size)
            .map(|_| Individual::new(num_genes, &target, &mut rng))
            .collect();

        Self {
            population_size,
            num_genes,
            mutation_rate,
            max_generations,
            target,
            population,
            max_population_size: population_size * 2,
            rng,
            report: Report::default(),
        }
    }

    pub fn run(mut self) -> Report {
        for generation in 0..self.max_generations {
            self.population
                .sort_unstable_by(|a, b| b.fitness.cmp(&a.fitness));

            println!(
                "Generation {}: Best fitness = {}, Genes = {:?}",
                generation, self.population[0].fitness, self.population[0].genes
            );

            let new_individuals: Vec<Individual> = (0..self.population_size)
                .map(|_| {
                    let parent1 = &self.population[self.rng.gen_range(0..self.population.len())];
                    let parent2 = &self.population[self.rng.gen_range(0..self.population.len())];
                    let mut offspring = parent1.crossover(parent2, &self.target, &mut self.rng);
                    offspring.mutate(self.mutation_rate, &self.target, &mut self.rng);
                    offspring
                })
                .collect();

            self.population.extend(new_individuals);

            if self.population.len() > self.max_population_size {
                self.population
                    .sort_unstable_by(|a, b| b.fitness.cmp(&a.fitness));
                self.population.truncate(self.max_population_size);
            }

            self.report.generations.push(GenerationReport {
                generation,
                best_fitness: self.population[0].fitness,
                best_genome: self.population[0].genes.clone(),
                population_size: self.population.len(),
            });
        }
        self.report
    }
}
