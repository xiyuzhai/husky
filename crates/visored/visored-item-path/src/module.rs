use crate::*;
use husky_coword::Coword;
use latex_environment::path::LxEnvironmentPath;
use latex_vfs::path::LxFilePath;
use rustc_hash::FxHashMap;
use visored_prelude::division::VdDivisionLevel;

#[salsa::interned(constructor = new_inner)]
pub struct VdModulePath {
    pub data: VdModulePathData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VdModulePathData {
    Root(LxFilePath),
    Division {
        parent: VdModulePath,
        division_kind: VdDivisionLevel,
        disambiguator: u32,
    },
    Paragraph {
        parent: VdModulePath,
        disambiguator: u32,
    },
    Environment {
        parent: VdModulePath,
        environment_path: LxEnvironmentPath,
        disambiguator: u32,
    },
}

impl VdModulePath {
    pub fn new_root(db: &::salsa::Db, file_path: LxFilePath) -> Self {
        Self::new_inner(db, VdModulePathData::Root(file_path))
    }

    fn new_child_from_tag_and_disambiguator(
        parent: VdModulePath,
        tag: VdModulePathTag,
        disambiguator: u32,
        db: &::salsa::Db,
    ) -> Self {
        let data = match tag {
            VdModulePathTag::Division(division_kind) => VdModulePathData::Division {
                parent,
                division_kind,
                disambiguator,
            },
            VdModulePathTag::Paragraph => VdModulePathData::Paragraph {
                parent,
                disambiguator,
            },
            VdModulePathTag::Environment(environment_path) => VdModulePathData::Environment {
                parent,
                environment_path,
                disambiguator,
            },
        };
        Self::new_inner(db, data)
    }
}

impl VdModulePath {
    pub fn parent(self, db: &::salsa::Db) -> Option<Self> {
        match self.data(db) {
            VdModulePathData::Root(_) => None,
            VdModulePathData::Division { parent, .. } => Some(parent),
            VdModulePathData::Paragraph { parent, .. } => Some(parent),
            VdModulePathData::Environment { parent, .. } => Some(parent),
        }
    }

    pub fn show(&self, db: &::salsa::Db) -> String {
        match self.data(db) {
            VdModulePathData::Root(file_path) => "root".to_string(),
            VdModulePathData::Division {
                parent,
                division_kind,
                disambiguator,
            } => {
                format!("{}.{}", parent.show(db), division_kind)
            }
            VdModulePathData::Paragraph {
                parent,
                disambiguator,
            } => {
                format!("{}.paragraph{}", parent.show(db), disambiguator)
            }
            VdModulePathData::Environment {
                parent,
                environment_path,
                disambiguator,
            } => {
                format!(
                    "{}.{}",
                    parent.show(db),
                    environment_path.name().coword().data(db)
                )
            }
        }
    }
}

/// Data without parent and disambiguator
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdModulePathTag {
    Division(VdDivisionLevel),
    Paragraph,
    Environment(LxEnvironmentPath),
}

pub struct VdModulePathRegistry {
    parent: VdModulePath,
    pub(crate) map: FxHashMap<VdModulePathTag, u32>,
}

impl VdModulePathRegistry {
    pub fn new(parent: VdModulePath) -> Self {
        Self {
            parent,
            map: Default::default(),
        }
    }

    pub fn issue_new_division(
        &mut self,
        division_level: VdDivisionLevel,
        db: &::salsa::Db,
    ) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Division(division_level), db)
    }

    pub fn issue_new_paragraph(&mut self, db: &::salsa::Db) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Paragraph, db)
    }

    pub fn issue_new_environment(
        &mut self,
        environment_path: LxEnvironmentPath,
        db: &::salsa::Db,
    ) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Environment(environment_path), db)
    }

    fn issue_new_child(&mut self, tag: VdModulePathTag, db: &::salsa::Db) -> VdModulePath {
        let disambiguator = match self.map.get_mut(&tag) {
            None => {
                self.map.insert(tag, 1);
                0
            }
            Some(existing_disambiguator) => {
                let new_disambiguator = *existing_disambiguator;
                *existing_disambiguator += 1;
                new_disambiguator
            }
        };
        VdModulePath::new_child_from_tag_and_disambiguator(self.parent, tag, disambiguator, db)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_issue_new_child() {
        // Create a mock Salsa database

        let db = &DB::default();

        let file_path = LxFilePath::new(db, PathBuf::from("test.txt"));

        // Create a root path
        let root = VdModulePath::new_inner(&db, VdModulePathData::Root(file_path));

        // Create a registry with the root path
        let mut registry = VdModulePathRegistry {
            parent: root,
            map: FxHashMap::default(),
        };

        // Test multiple paragraphs (0 through 9)
        let mut paragraph_paths = Vec::new();
        for expected_disambiguator in 0..10 {
            let path = registry.issue_new_paragraph(&db);
            if let VdModulePathData::Paragraph { disambiguator, .. } = path.data(&db) {
                assert_eq!(disambiguator, expected_disambiguator);
                paragraph_paths.push(path);
            } else {
                panic!("Expected Paragraph");
            }
        }

        // Test multiple divisions (0 through 4)
        let mut division_paths = Vec::new();
        for expected_disambiguator in 0..5 {
            let path = registry.issue_new_division(VdDivisionLevel::Section, db);
            if let VdModulePathData::Division { disambiguator, .. } = path.data(db) {
                assert_eq!(disambiguator, expected_disambiguator);
                division_paths.push(path);
            } else {
                panic!("Expected Division");
            }
        }

        // Test multiple environments (0 through 7)
        let mut env_paths = Vec::new();
        let equation = LxEnvironmentPath::new("equation", db);
        for expected_disambiguator in 0..8 {
            let path = registry.issue_new_environment(equation, db);
            if let VdModulePathData::Environment { disambiguator, .. } = path.data(db) {
                assert_eq!(disambiguator, expected_disambiguator);
                env_paths.push(path);
            } else {
                panic!("Expected Environment");
            }
        }

        // Verify final counts in the registry
        assert_eq!(*registry.map.get(&VdModulePathTag::Paragraph).unwrap(), 10);
        assert_eq!(
            *registry
                .map
                .get(&VdModulePathTag::Division(VdDivisionLevel::Section))
                .unwrap(),
            5
        );
        assert_eq!(
            *registry
                .map
                .get(&VdModulePathTag::Environment(equation))
                .unwrap(),
            8
        );

        // Verify we can still create new items after many iterations
        let last_paragraph = registry.issue_new_paragraph(&db);
        if let VdModulePathData::Paragraph { disambiguator, .. } = last_paragraph.data(&db) {
            assert_eq!(disambiguator, 10);
        } else {
            panic!("Expected Paragraph");
        }
    }
}
