use crate::ui::IsUi;
use crate::ui::UiTextureId;
use husky_visual_protocol::synchrotron::VisualSynchrotron;
use husky_visual_protocol::visual::image::ImageVisual;
use rustc_hash::FxHashMap;

pub struct VisualUiCache<Ui: IsUi> {
    //todo: optimize by LRU??
    pub(crate) texture_handles: FxHashMap<ImageVisual, Ui::TextureHandle>,
}

impl<Ui: IsUi> Default for VisualUiCache<Ui> {
    fn default() -> Self {
        Self {
            texture_handles: Default::default(),
        }
    }
}

impl<Ui: IsUi> VisualUiCache<Ui> {
    #[inline(always)]
    pub(super) fn texture_id(
        &mut self,
        image: ImageVisual,
        visual_synchrotron: &VisualSynchrotron,
        ui: &Ui,
    ) -> UiTextureId<Ui> {
        self.texture_id_aux(image, || ui.load_texture(image, visual_synchrotron))
    }

    // get or insert with
    fn texture_id_aux(
        &mut self,
        image: ImageVisual,
        f: impl FnOnce() -> Ui::TextureHandle,
    ) -> UiTextureId<Ui> {
        use crate::ui::IsTextureHandle;
        self.texture_handles.entry(image).or_insert_with(f).id()
    }
}
