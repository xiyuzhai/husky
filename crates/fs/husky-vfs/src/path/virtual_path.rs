use husky_print_utils::p;

use super::*;
use std::{
    fmt::Debug,
    path::{Path, PathBuf},
};

/// `VirtualPath` is the path relative to the current dir of the current program,
/// it's guaranteed that equivalent paths are interned to the same id
#[salsa::interned(db = VfsDb, jar = VfsJar, override_debug)]
pub struct VirtualPath {
    #[return_ref]
    _data: VirtualPathBuf,
}

impl ::salsa::DebugWithDb for VirtualPath {
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &salsa::Db,
    ) -> std::fmt::Result {
        self.data(db).fmt(f)
    }
}

impl VirtualPath {
    #[inline(always)]
    pub fn data<'a>(self, db: &'a ::salsa::Db) -> &'a Path {
        self._data(db)
    }

    pub fn abs_path(self, db: &::salsa::Db) -> VfsResult<PathBuf> {
        db.vfs_cache()
            .current_dir()
            .join(&self.data(db))
            .canonicalize()
            .map_err(|e| {
                p!(db.vfs_cache().current_dir().join(&self.data(db)), e);
                todo!()
            })
    }

    pub fn join(self, path: impl AsRef<Path>, db: &::salsa::Db) -> Self {
        VirtualPath::new(db, VirtualPathBuf(self.data(db).join(path)))
    }

    pub fn file(self, db: &::salsa::Db) -> VfsResult<File> {
        db.file_from_virtual_path(self)
    }

    pub fn exists(self, db: &::salsa::Db) -> VfsResult<bool> {
        match self.file(db) {
            Ok(file) => match file.content(db) {
                FileContent::NotExists => Ok(false),
                FileContent::OnDisk(_) => Ok(true),
                FileContent::LiveDoc(_) => todo!(),
                FileContent::Directory(_) => Ok(true),
                FileContent::Err(_) => todo!(),
            },
            Err(e) => match e {
                VfsError::FileNotExists(_) => todo!(),
                VfsError::Io {
                    path: _,
                    error_message: _,
                } => todo!(),
                VfsError::Io2(_) => todo!(),
                VfsError::NotSourceFile(_) => todo!(),
                VfsError::FailToAbsolutize {
                    path: _,
                    error_message: _,
                } => todo!(),
                VfsError::FailToDiff => todo!(),
                VfsError::ModulePathResolveFailure => todo!(),
                VfsError::MinimalToml(_) => todo!(),
                VfsError::PackageIdent => todo!(),
                VfsError::PathUtils(_) => todo!(),
                VfsError::FsSpecs(_) => todo!(),
                VfsError::FailToReadPackageNameFromManifest => todo!(),
            },
        }
    }

    pub fn text<'a>(self, db: &'a ::salsa::Db) -> VfsResult<Option<&'a str>> {
        let file = self.file(db)?;
        Ok(file.text(db)?)
    }

    pub fn text_expected<'a>(self, db: &'a ::salsa::Db) -> VfsResult<&'a str> {
        let file = self.file(db)?;
        file.text(db)?.ok_or(VfsError::FileNotExists(self))
    }
}

impl VirtualPath {
    // todo: room for optimization when path is owned
    pub fn try_new(db: &::salsa::Db, path: impl AsRef<Path>) -> VfsResult<Self> {
        Ok(Self::new(db, VirtualPathBuf::try_new(db, path.as_ref())?))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct VirtualPathBuf(PathBuf);

#[test]
fn test_absolute_path_debug() {
    let _db = DB::default();
    // let abs_path = VirtualPath::new(path);
}

impl VirtualPathBuf {
    pub fn try_new(db: &::salsa::Db, path: &Path) -> VfsResult<Self> {
        let diff = |path: &Path| -> VfsResult<_> {
            pathdiff::diff_paths(path, db.vfs_cache().current_dir()).ok_or(VfsError::FailToDiff)
        };
        let diff_path = if path.is_absolute() {
            diff(path)
        } else {
            diff(
                &std::path::absolute(&path).map_err(|e| VfsError::FailToAbsolutize {
                    path: path.to_owned(),
                    error_message: e.to_string(),
                })?,
            )
        }?;
        Ok(VirtualPathBuf(diff_path))
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl std::ops::Deref for VirtualPathBuf {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
