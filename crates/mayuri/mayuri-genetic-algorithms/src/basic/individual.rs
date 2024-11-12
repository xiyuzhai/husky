use super::*;

#[derive(Clone)]
pub struct Individual {
    pub genes: Vec<bool>,
    pub fitness: i32,
}

impl Individual {
    pub fn new(num_genes: usize, target: &[bool], rng: &mut ChaCha8Rng) -> Self {
        let genes: Vec<bool> = (0..num_genes).map(|_| rng.gen()).collect();
        let fitness = Self::calculate_fitness_value(&genes, target);
        Self { genes, fitness }
    }

    pub fn update_fitness(&mut self, target: &[bool]) {
        self.fitness = Self::calculate_fitness_value(&self.genes, target);
    }

    pub fn calculate_fitness_value(genes: &[bool], target: &[bool]) -> i32 {
        genes
            .iter()
            .zip(target.iter())
            .filter(|&(a, b)| a == b)
            .count() as i32
    }

    pub fn mutate(&mut self, mutation_rate: f64, target: &[bool], rng: &mut ChaCha8Rng) {
        for gene in &mut self.genes {
            if rng.gen::<f64>() < mutation_rate {
                *gene = !*gene;
            }
        }
        self.update_fitness(target);
    }

    pub fn crossover(
        &self,
        other: &Individual,
        target: &[bool],
        rng: &mut ChaCha8Rng,
    ) -> Individual {
        let crossover_point = rng.gen_range(0..self.genes.len());
        let new_genes: Vec<bool> = self.genes[..crossover_point]
            .iter()
            .chain(&other.genes[crossover_point..])
            .cloned()
            .collect();

        let fitness = Self::calculate_fitness_value(&new_genes, target);
        Individual {
            genes: new_genes,
            fitness,
        }
    }
}
