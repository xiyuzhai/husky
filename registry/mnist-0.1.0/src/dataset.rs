use crate::*;

lazy_static::lazy_static! {
    pub(crate) static ref MNIST_DATASET: MnistDataset = MnistDataset::default();
}

pub struct MnistDataset {
    inputs: Vec<BinaryImage28>,
    labels: Vec<MnistLabel>,
    permutation: Vec<u32>,
}

impl Default for MnistDataset {
    fn default() -> Self {
        Self::new(35016232u64)
    }
}

impl MnistDataset {
    fn new(seed: u64) -> Self {
        let (inputs, labels) = load_mnist_inputs_and_labels();
        let permutation = husky_rng_utils::generate_random_permutation(60000, seed);
        debug_assert_eq!(permutation[0], 17306);
        Self {
            inputs,
            labels,
            permutation,
        }
    }

    pub fn input(&self, input_id: MnistInputId) -> &BinaryImage28 {
        &self.inputs[self.index(input_id)]
    }

    pub fn input_leashed(&'static self, input_id: MnistInputId) -> Leash<BinaryImage28> {
        Leash(&self.inputs[self.index(input_id)])
    }

    pub fn label(&self, input_id: MnistInputId) -> MnistLabel {
        self.labels[self.index(input_id)]
    }

    fn index(&self, input_id: MnistInputId) -> usize {
        self.permutation[input_id.index()] as usize
    }

    pub fn inputs(&self) -> impl Iterator<Item = &BinaryImage28> {
        (0..self.inputs.len())
            .into_iter()
            .map(|index| MnistInputId::from_index(index))
            .map(|input_id| self.input(input_id))
    }
}

fn load_mnist_inputs_and_labels() -> (Vec<BinaryImage28>, Vec<MnistLabel>) {
    let mut images: Vec<BinaryImage28> = vec![];
    let mut labels: Vec<MnistLabel> = vec![];
    let mut dir: &std::path::Path = &std::env::current_dir().unwrap();
    while dir.file_name().unwrap().to_str().unwrap() != "husky" {
        dir = dir.parent().unwrap();
    }
    let file_content: Vec<u8> = match std::fs::read(dir.join("data/cv/mnist-binary-images")) {
        Ok(file_content) => file_content,
        Err(_e) => {
            println!(
                "current dir = {:?}, dir = {dir:?}",
                (std::env::current_dir())
            );
            todo!()
        }
    };
    assert_eq!(file_content.len(), 60000 * (1 + 28 * 4));
    for input_idx in 0..60000 {
        let base = input_idx * (1 + 28 * 4);
        labels.push(file_content[base].into());
        images.push(BinaryImage28::read(
            &file_content[(base + 1)..(base + 1 + 28 * 4)],
        ));
    }
    assert_eq!(labels[0], 5.into());
    assert_eq!(labels.len(), 60000);
    assert_eq!(images.len(), 60000);
    (images, labels)
}

impl BinaryImage28 {
    fn read(content: &[u8]) -> Self {
        assert_eq!(content.len(), 28 * 4);
        let mut padded_rows = [0; 30];
        for i in 0..28 {
            let mut row = 0u32;
            for k in 0..4 {
                row |= (content[i * 4 + k] as u32) << (3 - k) * 8;
            }
            padded_rows[i + 1] = row;
        }
        Self(padded_rows)
    }
}
