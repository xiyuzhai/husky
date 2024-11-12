pub struct DisplayIt<T>(pub T);

impl<T: std::fmt::Display> std::fmt::Debug for DisplayIt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
