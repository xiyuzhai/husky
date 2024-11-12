use super::*;
use crate::jar::VfsDbInner;
use husky_adversarial_utils::new_rand_string2;
use std::panic::AssertUnwindSafe;

#[derive(Debug, PartialEq, Eq, Deserialize, Serialize)]
pub(super) enum VfsAdversarial {
    InsertNewLine { position: usize },
    InsertSpace { position: usize, nspace: u8 },
    InsertString { position: usize, insertion: String },
    DeleteToEof { position: usize },
    DeleteToEol { position: usize, delete_eol: bool },
}

impl VfsAdversarial {
    const NUMBER_OF_VARIANTS: u8 = 4;

    pub(super) fn new_rand(text: &str, rng: &mut XRng) -> Option<Self> {
        let kind: u8 = rng.rand_range(0..VfsAdversarial::NUMBER_OF_VARIANTS);
        match kind {
            0 => Self::new_rand_insert_new_line(text, rng),
            1 => Self::new_rand_insert_space(text, rng),
            2 => Self::new_rand_insert_string(text, rng),
            3 => Self::new_rand_delete_to_eof(text, rng),
            4 => Self::new_rand_delete_to_eol(text, rng),
            _ => unreachable!(),
        }
    }

    pub(super) fn test(
        &self,
        db: &mut Db,
        module_path: ModulePath,
        f: &impl Fn(&::salsa::Db),
    ) -> VfsResult<()> {
        let original_text = module_path.raw_text(db);
        let original_text = original_text.to_owned();
        let edited_text = self.edit(&original_text);
        let Some(path) = module_path.virtual_path(db) else {
            todo!()
        };
        let file = db.file_from_virtual_path(path).unwrap();
        // edit text using adversarial
        file.set_content(db.vfs_db_mut())?
            .to(FileContent::LiveDoc(edited_text));
        // run the function to see if it panicked
        let catch_unwind = std::panic::catch_unwind(AssertUnwindSafe(|| f(db)));
        // then rollback to original
        file.set_content(db)?
            .to(FileContent::LiveDoc(original_text));
        match catch_unwind {
            Ok(_) => Ok(()),
            Err(_) => Err(todo!()),
        }
    }

    fn edit(&self, text: &str) -> String {
        self.to_edit(text).apply(text)
    }

    fn to_edit(&self, _text: &str) -> VfsEdit {
        match self {
            VfsAdversarial::InsertNewLine { position } => VfsEdit::InsertString {
                position: *position,
                insertion: "\n".into(),
            },
            VfsAdversarial::InsertSpace { position, nspace } => VfsEdit::InsertString {
                position: *position,
                insertion: (0..*nspace)
                    .into_iter()
                    .map(|_| ' ')
                    .collect::<String>()
                    .into(),
            },
            VfsAdversarial::InsertString {
                position,
                insertion,
            } => VfsEdit::InsertString {
                position: *position,
                insertion: insertion.into(),
            },
            VfsAdversarial::DeleteToEof { position } => VfsEdit::DeleteToEof {
                position: *position,
            },
            VfsAdversarial::DeleteToEol {
                position,
                delete_eol,
            } => VfsEdit::DeleteToEol {
                position: *position,
                delete_eol: *delete_eol,
            },
        }
    }

    fn new_rand_insert_new_line(text: &str, rng: &mut XRng) -> Option<VfsAdversarial> {
        Some(VfsAdversarial::InsertNewLine {
            position: new_rand_position(text, rng)?,
        })
    }

    fn new_rand_insert_space(text: &str, rng: &mut XRng) -> Option<VfsAdversarial> {
        Some(VfsAdversarial::InsertSpace {
            position: new_rand_position(text, rng)?,
            nspace: rng.try_randint(0..5)?,
        })
    }

    fn new_rand_insert_string(text: &str, rng: &mut XRng) -> Option<VfsAdversarial> {
        static PIECES: &'static [&'static str] = &[
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q",
            "r", "s", "t", "u", "v", "w", "x", "y", "z", "$", "%",
        ];
        Some(VfsAdversarial::InsertString {
            position: new_rand_position(text, rng)?,
            insertion: new_rand_string2(rng, 5, PIECES),
        })
    }

    fn new_rand_delete_to_eof(text: &str, rng: &mut XRng) -> Option<VfsAdversarial> {
        Some(VfsAdversarial::DeleteToEof {
            position: new_rand_position(text, rng)?,
        })
    }

    fn new_rand_delete_to_eol(text: &str, rng: &mut XRng) -> Option<VfsAdversarial> {
        Some(VfsAdversarial::DeleteToEol {
            position: new_rand_position(text, rng)?,
            delete_eol: rng.randbool(),
        })
    }
}

fn new_rand_position(text: &str, rng: &mut XRng) -> Option<usize> {
    rng.try_randint(0..text.chars().count())
}
