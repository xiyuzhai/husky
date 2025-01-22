#![feature(async_closure)]
mod entry;
pub mod error;
mod save;
pub mod seed;
#[cfg(test)]
mod tests;
pub mod traits;

use self::{
    entry::LlmCacheEntry,
    error::{DiskCacheError, DiskCacheResult},
    traits::{IsDiskCacheRequest, IsDiskCacheResponse},
};
use attach::Attach;
use chrono::Duration;
use dashmap::DashMap;
use save::LlmCacheSaveThread;
use seed::IsDiskCacheSeed;
use serde::{Deserialize, Serialize};
use std::path::Path;
use std::sync::Arc;
use std::{fs, path::PathBuf};
use std::{io, sync::RwLock};
#[cfg(test)]
use tempfile;

pub struct DiskCache<Db, Seed, Request, Response>
where
    Seed: IsDiskCacheSeed,
    Request: IsDiskCacheRequest,
    Response: IsDiskCacheResponse,
{
    db: Db,
    tokio_runtime: Arc<tokio::runtime::Runtime>,
    path: PathBuf,
    entries: RwLock<Vec<LlmCacheEntry<Seed, Request, Response>>>,
    indices: DashMap<(Seed, Request), usize>,
    save_thread: LlmCacheSaveThread<Db, Seed, Request, Response>,
}

impl<Db, Seed, Request, Response> DiskCache<Db, Seed, Request, Response>
where
    Db: Attach,
    Seed: IsDiskCacheSeed,
    Request: IsDiskCacheRequest,
    Response: IsDiskCacheResponse,
{
    /// Creates a new LLM cache that stores request-response pairs at the specified path.
    ///
    /// # Arguments
    /// * `path` - Path where the cache file will be stored
    ///
    /// # Returns
    /// * `Ok(DiskCache)` - A new cache instance
    /// * `Err(LlmCacheError)` - If the cache file is locked or there are IO errors
    ///
    /// # Example
    /// ```
    /// use std::path::PathBuf;
    /// use disk_cache::DiskCache;
    ///
    /// let db = ();
    /// let temp_dir = tempfile::tempdir().unwrap();
    /// let cache_path = temp_dir.path().join("cache.json");
    /// let tokio_runtime = std::sync::Arc::new(tokio::runtime::Runtime::new().unwrap());
    /// let cache: DiskCache<(), (), String, String> = DiskCache::new(db, tokio_runtime, cache_path).unwrap();
    /// ```
    pub fn new(
        db: Db,
        tokio_runtime: Arc<tokio::runtime::Runtime>,
        path: PathBuf,
    ) -> DiskCacheResult<Self> {
        fn setup_lock_file(path: &Path) -> DiskCacheResult<()> {
            use lazy_static::lazy_static;
            use std::sync::Mutex;

            lazy_static! {
                static ref CLEANUP_HANDLER: Mutex<CleanupHandler> =
                    Mutex::new(CleanupHandler::new());
            }

            struct CleanupHandler {
                paths: Vec<PathBuf>,
            }

            impl CleanupHandler {
                fn new() -> Self {
                    if let Err(e) = ctrlc::set_handler(move || {
                        for path in &CLEANUP_HANDLER.lock().unwrap().paths {
                            let _ = fs::remove_file(lock_file_path(path));
                        }
                        std::process::exit(0);
                    }) {
                        eprintln!("Warning: Failed to set Ctrl+C handler: {}", e);
                    }

                    Self { paths: Vec::new() }
                }

                fn register(&mut self, path: PathBuf) {
                    self.paths.push(path);
                }
            }

            // check lock file does not exist
            let lock_file_path = lock_file_path(path);
            if lock_file_path.exists() {
                return Err(DiskCacheError::CacheFileLockedByAnotherProcess { lock_file_path });
            }

            let mut cleanup_handler = CLEANUP_HANDLER.lock().unwrap();

            // create lock file
            fs::File::create(lock_file_path)
                .map_err(|e| DiskCacheError::Io(path.to_path_buf(), e))?;

            // Register this lock file with the cleanup handler
            cleanup_handler.register(path.to_path_buf());

            Ok(())
        }

        // Create directory if it doesn't exist
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| DiskCacheError::Io(path.clone(), e))?;
        }

        setup_lock_file(&path)?;

        // Try to load existing cache
        let entries: Vec<LlmCacheEntry<Seed, Request, Response>> = if path.exists() {
            let contents =
                fs::read_to_string(&path).map_err(|e| DiskCacheError::Io(path.clone(), e))?;
            db.attach(|| serde_json::from_str(&contents).unwrap_or_default())
        } else {
            Default::default()
        };

        let save_thread = LlmCacheSaveThread::new(db, path.clone(), entries.clone());

        let indices = entries
            .iter()
            .enumerate()
            .map(|(i, e)| ((e.seed, e.request.clone()), i))
            .collect();
        Ok(Self {
            db,
            tokio_runtime,
            path,
            entries: RwLock::new(entries),
            indices,
            save_thread,
        })
    }
}

impl<Db, Seed, Request, Response> DiskCache<Db, Seed, Request, Response>
where
    Db: Attach,
    Seed: IsDiskCacheSeed,
    Request: IsDiskCacheRequest,
    Response: IsDiskCacheResponse,
{
    pub fn get_or_call<E>(
        &self,
        seed: Seed,
        request: Request,
        f: impl async FnOnce(&Request) -> Result<Response, E>,
    ) -> Result<Response, E>
    where
        E: From<DiskCacheError>,
    {
        if let Some(index) = self.indices.get(&(seed, request.clone())) {
            return Ok(self.entries.read().unwrap()[*index].response.clone());
        }
        let response = self.get_or_call_aux(seed, request, f)?;
        Ok(response)
    }

    fn get_or_call_aux<E>(
        &self,
        seed: Seed,
        request: Request,
        f: impl async FnOnce(&Request) -> Result<Response, E>,
    ) -> Result<Response, E>
    where
        E: From<DiskCacheError>,
    {
        let mut entries = self.entries.write().unwrap();
        // check again in case another thread has added the entry
        if let Some(index) = self.indices.get(&(seed, request.clone())) {
            return Ok(entries[*index].response.clone());
        }
        let response = self.tokio_runtime.block_on(f(&request))?;
        let new_entry = LlmCacheEntry::new(seed, request.clone(), response.clone());
        entries.push(new_entry);
        self.save_thread.save(&entries)?;
        self.indices
            .insert((seed, request.clone()), entries.len() - 1);
        Ok(response)
    }
}

impl<Db, Seed, Request, Response> Drop for DiskCache<Db, Seed, Request, Response>
where
    Seed: IsDiskCacheSeed,
    Request: IsDiskCacheRequest,
    Response: IsDiskCacheResponse,
{
    fn drop(&mut self) {
        fs::remove_file(lock_file_path(&self.path)).unwrap();
    }
}

fn lock_file_path(path: &Path) -> PathBuf {
    let ext = path.extension().unwrap_or_default().to_str().unwrap_or("");
    if ext.is_empty() {
        // No extension: just add ".lock"
        path.with_extension("lock")
    } else {
        // Has extension: append ".lock" to the existing extension
        path.with_extension(format!("{}.lock", ext))
    }
}

#[test]
fn lock_file_path_works() {
    assert_eq!(
        lock_file_path(Path::new("path/to/cache")),
        PathBuf::from("path/to/cache.lock")
    );
    assert_eq!(
        lock_file_path(Path::new("path/to/cache.json")),
        PathBuf::from("path/to/cache.json.lock")
    );
}
