use shifted_unsigned_int::ShiftedU32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(ShiftedU32);

impl FileId {
    pub(crate) fn new(file: u32) -> Self {
        Self(file.into())
    }
}

impl Into<u32> for FileId {
    fn into(self) -> u32 {
        self.0.into()
    }
}
