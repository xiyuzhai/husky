pub mod cache;

use super::*;
use crate::ui::{IsTextureHandle, IsUi};
#[cfg(feature = "egui")]
use egui::{pos2, Rect, Sense};
use husky_visual_protocol::{
    synchrotron::VisualSynchrotron,
    visual::{image::ImageVisual, primitive::PrimitiveVisual, Visual},
};
use rustc_hash::FxHashMap;

pub trait VisualUi<Ui: IsUi>: Copy {
    fn ui(
        self,
        rect: Option<Ui::Rect>,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut cache::VisualUiCache<Ui>,
        ui: &mut Ui,
    );
}

#[cfg(feature = "egui")]
impl VisualUi<::egui::Ui> for Visual {
    fn ui(
        self,
        rect: Option<Rect>,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut cache::VisualUiCache<::egui::Ui>,
        ui: &mut ::egui::Ui,
    ) {
        match self {
            Visual::Void => (),
            Visual::Image(slf) => slf.ui(rect, visual_synchrotron, cache, ui),
            Visual::Math(_) => todo!(),
            Visual::Mesh(_) => todo!(),
            Visual::Primitive(slf) => slf.ui(rect, visual_synchrotron, cache, ui),
            Visual::RichText(_) => todo!(),
            Visual::Shape(_) => todo!(),
            Visual::Text(_) => todo!(),
            Visual::Video(_) => todo!(),
            Visual::Group(_) => todo!(),
            Visual::Error => todo!(),
        }
    }
}

#[cfg(feature = "egui")]
impl VisualUi<::egui::Ui> for ImageVisual {
    fn ui(
        self,
        rect: Option<Rect>,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut cache::VisualUiCache<::egui::Ui>,
        ui: &mut ::egui::Ui,
    ) {
        match rect {
            Some(rect) => ui.paint_image(
                cache.texture_id(self, visual_synchrotron, ui),
                rect,
                Rect::from_min_max(pos2(0.0, 0.0), pos2(1.0, 1.0)),
                ::egui::Color32::WHITE,
            ),
            None => todo!(),
        }
    }
}

#[cfg(feature = "egui")]
impl VisualUi<::egui::Ui> for PrimitiveVisual {
    fn ui(
        self,
        rect: Option<Rect>,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut cache::VisualUiCache<::egui::Ui>,
        ui: &mut ::egui::Ui,
    ) {
        match self {
            PrimitiveVisual::I8(i) => ui.label(format!("{}", i)),
            PrimitiveVisual::F32(f) => ui.label(format!("{}", f)),
            PrimitiveVisual::F64(f) => ui.label(format!("{}", f)),
        };
    }
}
