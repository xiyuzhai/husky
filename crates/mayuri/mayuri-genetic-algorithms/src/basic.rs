mod individual;
mod lab;
mod report;

use rand::*;
use rand_chacha::ChaCha8Rng;
use std::cmp::Ordering;

#[test]
fn mayuri_genetic_algorithms_works() {
    use crate::basic::lab::Lab;
    use expect_test::expect_file;

    let mut lab = Lab::new(
        100,                                                              // population_size
        10,                                                               // num_genes
        0.01,                                                             // mutation_rate
        100,                                                              // max_generations
        vec![true, true, true, true, true, true, true, true, true, true], // target
        42,                                                               // seed
    );

    let report = lab.run();

    expect_file!["../expect-files/mayuri_basic_genetic_algorithms_works.txt"]
        .assert_debug_eq(&report);
}
