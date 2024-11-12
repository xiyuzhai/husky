use crate::resolution::{
    command::{VdCompleteCommandGlobalResolution, VdCompleteCommandGlobalResolutionMap},
    letter::{VdLetterGlobalResolution, VdLetterGlobalResolutionMap},
    punctuation::{VdPunctuationGlobalResolution, VdPunctuationGlobalResolutionMap},
};
use latex_command::path::LxCommandPath;
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::{LxMathPunctuation, LxMathPunctuationMap};

pub struct VdDefaultGlobalResolutionTable {
    punctuation_resolution_map: VdPunctuationGlobalResolutionMap,
    complete_command_resolution_map: VdCompleteCommandGlobalResolutionMap,
    letter_resolution_map: VdLetterGlobalResolutionMap,
}

impl VdDefaultGlobalResolutionTable {
    pub fn new(
        punctuation_resolution_map: VdPunctuationGlobalResolutionMap,
        complete_command_resolution_map: VdCompleteCommandGlobalResolutionMap,
        letter_resolution_map: VdLetterGlobalResolutionMap,
    ) -> Self {
        Self {
            punctuation_resolution_map,
            complete_command_resolution_map,
            letter_resolution_map,
        }
    }
}

impl VdDefaultGlobalResolutionTable {
    pub fn resolve_punctuation(
        &self,
        punctuation: LxMathPunctuation,
    ) -> Option<VdPunctuationGlobalResolution> {
        self.punctuation_resolution_map[punctuation]
    }

    pub fn resolve_complete_command(
        &self,
        command_path: LxCommandPath,
    ) -> Option<&VdCompleteCommandGlobalResolution> {
        self.complete_command_resolution_map.get(&command_path)
    }

    pub fn resolve_letter(&self, letter: LxMathLetter) -> Option<VdLetterGlobalResolution> {
        self.letter_resolution_map.get(&letter).copied()
    }
}
