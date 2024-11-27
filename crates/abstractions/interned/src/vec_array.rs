pub struct VecArray<T, const N: usize> {
    data: Vec<T>,
}

impl<T: std::ops::Deref, const N: usize> std::ops::Deref for VecArray<T, N> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T, const N: usize> VecArray<T, N> {
    pub fn new() -> Self {
        let data = Vec::with_capacity(N);
        Self { data }
    }

    pub fn is_full(&self) -> bool {
        self.data.len() == N
    }

    pub fn push(&mut self, t: T) {
        assert!(!self.is_full());
        self.data.push(t);
    }

    pub fn last(&self) -> Option<&T> {
        self.data.last()
    }

    pub(crate) fn len(&self) -> usize {
        self.data.len()
    }
}
