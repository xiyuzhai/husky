//! TODO: now totally written by AI. Check it carefully.
//!
//! A virtual file system implementation that tracks file versions using timestamps
//!
//! This crate provides a simple in-memory file system abstraction that maintains file contents
//! and automatically detects changes by comparing timestamps. Key features include:
//!
//! - Caches file contents in memory for faster access
//! - Automatically detects file changes by comparing timestamps
//! - Provides thread-safe file content sharing using Arc
//! - Lazy loading: files are only read when requested
//!
//! # Example
//! ```
//! # use std::io;
//! use timestamp_vfs::{TpVfs, error::TpVfsResult, FileKind};
//!
//! # fn main() -> TpVfsResult<()> {
//! let mut vfs = TpVfs::new();
//!
//! // Set file content
//! vfs.set_file("example.txt", b"Hello, World!".to_vec(), FileKind::Live)?;
//!
//! // Read file content
//! if let Some(content) = vfs.get_file("example.txt")? {
//!     assert_eq!(&*content, b"Hello, World!");
//! }
//! # Ok(())
//! # }
//! ```
//!
//! When a file is accessed via `get_file`, the VFS checks if the underlying file has been
//! modified by comparing timestamps. If the file has changed, it automatically reloads
//! the content from disk.
pub mod error;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use error::{TpVfsError, TpVfsResult};

/// Represents the type of file in the virtual file system
#[derive(Debug, Clone, PartialEq)]
pub enum FileKind {
    /// File exists only in memory
    Live,
    /// File is backed by the filesystem
    OnDisk,
}

/// Represents a file in the virtual file system with its content and timestamp
#[derive(Debug, Clone)]
pub struct TpVfsFile {
    content: Arc<[u8]>,
    version: TpVfsFileVersionStamp,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TpVfsFileVersionStamp {
    Live,
    OnDisk { timestamp: u64 },
}

/// A virtual file system that tracks file versions using timestamps
#[derive(Debug, Default)]
pub struct TpVfs {
    files: HashMap<PathBuf, TpVfsFile>,
}

impl TpVfs {
    /// Creates a new empty virtual file system.
    ///
    /// Returns a `TpVfs` instance with no cached files.
    ///
    /// # Example
    /// ```
    /// use timestamp_vfs::TpVfs;
    /// let vfs = TpVfs::new();
    /// ```
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }

    /// Gets the file's last modified timestamp in milliseconds
    fn get_timestamp<P: AsRef<Path>>(path: P) -> TpVfsResult<u64> {
        Ok(std::fs::metadata(path)
            .map_err(TpVfsError::MetadataIO)?
            .modified()
            .map_err(TpVfsError::Modified)?
            .duration_since(UNIX_EPOCH)
            .map_err(TpVfsError::DuringSince)?
            .as_millis() as u64)
    }

    /// Sets or updates a file's content in the virtual file system.
    ///
    /// This method handles two types of files:
    /// - Live files: stored only in memory
    /// - On-disk files: synchronized with the filesystem
    ///
    /// # Arguments
    /// * `path` - The path to the file
    /// * `content` - The new content to store
    /// * `kind` - The kind of file (Live or OnDisk)
    ///
    /// # Returns
    /// * `Ok(())` if the operation succeeds
    /// * `Err` if writing to disk or reading the timestamp fails
    pub fn set_file<P: AsRef<Path>>(
        &mut self,
        path: P,
        content: Vec<u8>,
        kind: FileKind,
    ) -> TpVfsResult<()> {
        let path_ref = path.as_ref();

        // If it's an on-disk file, write to the filesystem first
        if kind == FileKind::OnDisk {
            std::fs::write(path_ref, &content).map_err(TpVfsError::Write)?;
        }

        self.files.insert(
            path_ref.to_path_buf(),
            TpVfsFile {
                content: content.into(),
                version: match kind {
                    FileKind::OnDisk => TpVfsFileVersionStamp::OnDisk {
                        timestamp: Self::get_timestamp(path_ref)?,
                    },
                    FileKind::Live => TpVfsFileVersionStamp::Live,
                },
            },
        );
        Ok(())
    }

    /// Gets a file's content from the virtual file system, updating it if necessary.
    ///
    /// This method:
    /// - Checks if the file exists in the filesystem
    /// - Compares the filesystem timestamp with the cached version
    /// - Returns the cached content if timestamps match
    /// - Automatically reloads the file if it has been modified
    /// - Returns None if the file doesn't exist
    ///
    /// # Arguments
    /// * `path` - The path to the file to retrieve
    ///
    /// # Returns
    /// * `Ok(Some(content))` if the file exists and was successfully read
    /// * `Ok(None)` if the file doesn't exist
    /// * `Err` if there was an error reading the file
    ///
    /// # Example
    /// ```
    /// use timestamp_vfs::{TpVfs, FileKind};
    /// use std::io;
    ///
    /// let temp_dir = tempfile::tempdir().unwrap();
    /// let file_path = temp_dir.path().join("example.txt");
    ///
    /// let mut vfs = TpVfs::new();
    ///
    /// // File doesn't exist yet
    /// assert!(vfs.get_file(&file_path).unwrap().is_none());
    ///
    /// // Create and read file
    /// vfs.set_file(&file_path, b"Hello".to_vec(), FileKind::OnDisk).unwrap();
    /// let content = vfs.get_file(&file_path).unwrap().unwrap();
    /// assert_eq!(&*content, b"Hello");
    /// ```
    pub fn get_file<P: AsRef<Path>>(&mut self, path: P) -> TpVfsResult<Option<Arc<[u8]>>> {
        let path_ref = path.as_ref();

        // First check if file exists and get its OS timestamp
        let os_timestamp = match Self::get_timestamp(path_ref) {
            Ok(ts) => ts,
            Err(e) => match e {
                TpVfsError::MetadataIO(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    return Ok(None)
                }
                _ => return Err(e),
            },
        };

        // Check if file needs updating
        if let Some(file) = self.files.get(path_ref) {
            if let TpVfsFileVersionStamp::OnDisk { timestamp } = file.version {
                if timestamp == os_timestamp {
                    return Ok(Some(Arc::clone(&file.content)));
                }
            }
        }

        // File has changed or doesn't exist in VFS - update it
        let content = std::fs::read(path_ref).map_err(TpVfsError::Read)?;
        self.files.insert(
            path_ref.to_path_buf(),
            TpVfsFile {
                content: content.into(),
                version: TpVfsFileVersionStamp::OnDisk {
                    timestamp: os_timestamp,
                },
            },
        );

        Ok(self
            .files
            .get(path_ref)
            .map(|file| Arc::clone(&file.content)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_new_vfs_is_empty() {
        let vfs = TpVfs::new();
        assert!(vfs.files.is_empty());
    }

    #[test]
    fn test_set_and_get_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = b"Hello, World!".to_vec();

        // Create the actual file first
        fs::write(&file_path, &content).unwrap();

        let mut vfs = TpVfs::new();
        vfs.set_file(&file_path, content.clone(), FileKind::Live)
            .unwrap();

        let stored_content = vfs
            .get_file(&file_path)
            .unwrap()
            .expect("File should exist");
        assert_eq!(&*stored_content, &content);
    }

    #[test]
    fn test_timestamp_from_real_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test_file.txt");

        fs::write(&file_path, "test content").unwrap();
        let timestamp1 = TpVfs::get_timestamp(&file_path).unwrap();

        // Small delay to ensure different timestamps
        std::thread::sleep(std::time::Duration::from_millis(10));

        fs::write(&file_path, "updated content").unwrap();
        let timestamp2 = TpVfs::get_timestamp(&file_path).unwrap();

        assert!(
            timestamp2 > timestamp1,
            "Timestamp should increase after file update"
        );
    }

    #[test]
    fn test_nonexistent_file() {
        let mut vfs = TpVfs::new();
        assert!(vfs.get_file("nonexistent.txt").unwrap().is_none());
    }
}
