use crate::{hotkey::IsHotkeyBuffer, visual::cache::VisualUiCache};
use husky_visual_protocol::{synchrotron::VisualSynchrotron, visual::image::ImageVisual};

#[cfg(feature = "egui")]
pub mod egui;

pub trait IsUi: Sized {
    type Rect;
    type HotkeyBuffer: IsHotkeyBuffer;
    type TextureHandle: IsTextureHandle;
    type Color32;
    fn load_texture(
        &self,
        image: ImageVisual,
        visual_synchrotron: &VisualSynchrotron,
    ) -> Self::TextureHandle;
    fn paint_image(
        &self,
        texture_id: UiTextureId<Self>,
        rect: Self::Rect,
        uv: Self::Rect,
        tint: Self::Color32,
    );
    fn non_selectable_label(&mut self, text: &str);
}

/// trivial implementation
impl IsUi for () {
    type Rect = ();

    type HotkeyBuffer = ();

    type TextureHandle = ();

    type Color32 = ();

    fn load_texture(
        &self,
        image: ImageVisual,
        visual_synchrotron: &VisualSynchrotron,
    ) -> Self::TextureHandle {
    }

    fn paint_image(
        &self,
        texture_id: UiTextureId<Self>,
        rect: Self::Rect,
        uv: Self::Rect,
        tint: Self::Color32,
    ) {
    }

    fn non_selectable_label(&mut self, text: &str) {}
}

pub trait IsTextureHandle {
    type TextureId;

    fn id(&self) -> Self::TextureId;
}

// Trivial implementation for the unit type ()
impl IsTextureHandle for () {
    type TextureId = ();

    fn id(&self) -> Self::TextureId {
        ()
    }
}

pub type UiTextureId<Ui> = <<Ui as IsUi>::TextureHandle as IsTextureHandle>::TextureId;
