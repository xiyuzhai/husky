use crate::*;
use environment::VdEnvironmentPath;
use husky_coword::Coword;
use latex_vfs::path::LxFilePath;
use rustc_hash::FxHashMap;
use smallvec::*;
use visored_prelude::division::VdDivisionLevel;

#[interned::interned]
pub struct VdModulePath {
    pub data: VdModulePathData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VdModulePathData {
    Root(LxFilePath),
    Division {
        parent: VdModulePath,
        division_level: VdDivisionLevel,
        disambiguator: u32,
    },
    Paragraph {
        parent: VdModulePath,
        disambiguator: u32,
    },
    Environment {
        parent: VdModulePath,
        environment_path: VdEnvironmentPath,
        disambiguator: u32,
    },
}

impl VdModulePath {
    pub fn new_root(file_path: LxFilePath) -> Self {
        Self::new(VdModulePathData::Root(file_path))
    }

    fn new_child_from_tag_and_disambiguator(
        parent: VdModulePath,
        tag: VdModulePathTag,
        disambiguator: u32,
    ) -> Self {
        let data = match tag {
            VdModulePathTag::Division(division_level) => VdModulePathData::Division {
                parent,
                division_level: division_level,
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
        Self::new(data)
    }
}

impl VdModulePath {
    pub fn parent(self) -> Option<Self> {
        match *self.data() {
            VdModulePathData::Root(_) => None,
            VdModulePathData::Division { parent, .. } => Some(parent),
            VdModulePathData::Paragraph { parent, .. } => Some(parent),
            VdModulePathData::Environment { parent, .. } => Some(parent),
        }
    }

    pub fn show(&self) -> String {
        match *self.data() {
            VdModulePathData::Root(file_path) => "root".to_string(),
            VdModulePathData::Division {
                parent,
                division_level: division_level,
                disambiguator,
            } => {
                format!("{}.{}", parent.show(), division_level)
            }
            VdModulePathData::Paragraph {
                parent,
                disambiguator,
            } => {
                format!("{}.paragraph{}", parent.show(), disambiguator)
            }
            VdModulePathData::Environment {
                parent,
                environment_path,
                disambiguator,
            } => {
                format!("{}.{}", parent.show(), environment_path)
            }
        }
    }

    /// includes the module itself
    pub fn lineage(self) -> &'static [VdModulePath] {
        vd_module_lineage(self)
    }

    pub fn contains(self, other: VdModulePath) -> bool {
        other.lineage().contains(&self)
    }
}

/// includes the module itself
#[interned::memo]
fn vd_module_lineage(module_path: VdModulePath) -> SmallVec<[VdModulePath; 8]> {
    match module_path.parent() {
        Some(parent) => {
            let mut ancestry = vd_module_lineage(parent).to_smallvec();
            ancestry.push(module_path);
            ancestry
        }
        None => smallvec![module_path],
    }
}

#[test]
fn vd_module_ancestry_works() {}

/// Data without parent and disambiguator
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdModulePathTag {
    Division(VdDivisionLevel),
    Paragraph,
    Environment(VdEnvironmentPath),
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

    pub fn issue_new_division(&mut self, division_level: VdDivisionLevel) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Division(division_level))
    }

    pub fn issue_new_paragraph(&mut self) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Paragraph)
    }

    pub fn issue_new_environment(&mut self, environment_path: VdEnvironmentPath) -> VdModulePath {
        self.issue_new_child(VdModulePathTag::Environment(environment_path))
    }

    fn issue_new_child(&mut self, tag: VdModulePathTag) -> VdModulePath {
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
        VdModulePath::new_child_from_tag_and_disambiguator(self.parent, tag, disambiguator)
    }
}

impl std::fmt::Debug for VdModulePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdModulePath(`")?;
        self.show_aux(f)?;
        f.write_str("`)")
    }
}

impl VdModulePath {
    pub fn show_aux(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.parent() {
            Some(parent) => {
                parent.show_aux(f)?;
                f.write_str(".")?;
                match self.data() {
                    VdModulePathData::Root(lx_file_path) => unreachable!(),
                    VdModulePathData::Division {
                        parent,
                        division_level,
                        disambiguator,
                    } => write!(f, "{}{}", division_level, disambiguator + 1)?,
                    VdModulePathData::Paragraph {
                        parent,
                        disambiguator,
                    } => write!(f, "paragraph{}", disambiguator + 1)?,
                    VdModulePathData::Environment {
                        parent,
                        environment_path,
                        disambiguator,
                    } => write!(f, "{}{}", environment_path, disambiguator + 1)?,
                }
            }
            None => f.write_str("root")?,
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_issue_new_child() {
        // Create a mock Salsa database

        let file_path = LxFilePath::new(PathBuf::from("test.txt"));

        // Create a root path
        let root = VdModulePath::new_root(file_path);

        // Create a registry with the root path
        let mut registry = VdModulePathRegistry {
            parent: root,
            map: FxHashMap::default(),
        };

        // Test multiple paragraphs (0 through 9)
        let mut paragraph_paths = Vec::new();
        for expected_disambiguator in 0..10 {
            let path = registry.issue_new_paragraph();
            if let VdModulePathData::Paragraph { disambiguator, .. } = *path.data() {
                assert_eq!(disambiguator, expected_disambiguator);
                paragraph_paths.push(path);
            } else {
                panic!("Expected Paragraph");
            }
        }

        // Test multiple divisions (0 through 4)
        let mut division_paths = Vec::new();
        for expected_disambiguator in 0..5 {
            let path = registry.issue_new_division(VdDivisionLevel::Section);
            if let VdModulePathData::Division { disambiguator, .. } = *path.data() {
                assert_eq!(disambiguator, expected_disambiguator);
                division_paths.push(path);
            } else {
                panic!("Expected Division");
            }
        }

        // Test multiple environments (0 through 7)
        let mut env_paths = Vec::new();
        let equation = VdEnvironmentPath::Equation;
        for expected_disambiguator in 0..8 {
            let path = registry.issue_new_environment(equation);
            if let VdModulePathData::Environment { disambiguator, .. } = *path.data() {
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
        let last_paragraph = registry.issue_new_paragraph();
        if let VdModulePathData::Paragraph { disambiguator, .. } = *last_paragraph.data() {
            assert_eq!(disambiguator, 10);
        } else {
            panic!("Expected Paragraph");
        }
    }
}
