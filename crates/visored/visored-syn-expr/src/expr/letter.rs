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
        resolutions.extend(
            self.symbol_local_defn_table()
                .resolve_letter(token_idx_range, letter)
                .map(|idx| VdSynLetterSymbolResolution::Local(idx).into()),
        );
        // TODO: check other things, like annotations
        Ok(resolutions)
    }
}
