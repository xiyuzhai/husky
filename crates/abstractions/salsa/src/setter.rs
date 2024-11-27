use crate::input_field::InputFieldIngredient;
use crate::{AsId, Durability, Runtime};

#[must_use]
pub struct Setter<'setter, K, F> {
    runtime: &'setter mut Runtime,
    key: K,
    ingredient: &'setter mut InputFieldIngredient<K, F>,
    durability: Durability,
}

impl<'setter, K, F> Setter<'setter, K, F>
where
    K: Eq + AsId,
{
    pub fn new(
        runtime: &'setter mut Runtime,
        key: K,
        durability: Durability,
        ingredient: &'setter mut InputFieldIngredient<K, F>,
    ) -> Self {
        Setter {
            runtime,
            key,
            ingredient,
            durability,
        }
    }

    pub fn to(self, value: F) -> F {
        self.ingredient
            .store_mut(self.runtime, self.key, value, self.durability)
            .unwrap()
    }
}
