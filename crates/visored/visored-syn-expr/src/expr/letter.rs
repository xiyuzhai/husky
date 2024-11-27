use super::*;

impl<'a> VdSynSymbolBuilder<'a> {
    pub fn build_letter(
        &mut self,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> VdSynSymbolResolutionResult<VdSynSymbolResolutions> {
        let default_global_resolution = self
            .default_global_resolution_table()
            .resolve_letter(letter);
        let mut resolutions: VdSynSymbolResolutions = default_global_resolution
            .into_iter()
            .map(Into::into)
            .collect();
        if let Some(local_resolution) = self.build_letter_local_resolution(token_idx_range, letter)
        {
            resolutions.push(local_resolution);
        }
        // TODO: check other things, like annotations
        Ok(resolutions)
    }

    fn build_letter_local_resolution(
        &mut self,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> Option<VdSynSymbolResolution> {
        let local_resolutions = self.build_letter_local_resolutions(token_idx_range, letter);
        match *local_resolutions {
            [] => None,
            [single] => Some(single),
            _ => {
                todo!(
                    r#"
    letter = `{}`
    local_resolutions = {:#?}
    local_defn_storage = {:#?}"#,
                    letter,
                    local_resolutions,
                    self.symbol_local_defn_storage()
                )
            }
        }
    }

    fn build_letter_local_resolutions(
        &mut self,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> VdSynSymbolResolutions {
        self.symbol_local_defn_storage()
            .resolve_letter(self.current_module_path(), token_idx_range, letter)
            .map(|idx| VdSynLetterSymbolResolution::Local(idx).into())
            .collect()
    }
}
