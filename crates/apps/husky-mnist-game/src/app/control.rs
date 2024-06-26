use super::*;
use crate::op::history::OpTime;
use egui::Slider;
use husky_ml_task_interface::{pedestal::MlPedestal, InputId};

pub struct MnistControl {
    input_id: InputId,
    frame_idx: usize,
    number_of_frames: usize,
}

/// # constructors
impl MnistControl {
    pub(crate) fn new(db: &MnistDb) -> MnistControl {
        let input_id = InputId::from_index(0);
        let number_of_frames = db.op_frames(input_id).len();
        Self {
            input_id,
            frame_idx: 0,
            number_of_frames,
        }
    }
}

/// # getters
impl MnistControl {
    pub(crate) fn op_time(&self) -> OpTime {
        OpTime::from_index(self.frame_idx.into())
    }

    pub(crate) fn pedestal(&self) -> MlPedestal {
        MlPedestal::Specific(self.input_id)
    }
}

impl egui::Widget for &mut MnistControl {
    fn ui(self, ui: &mut egui::Ui) -> egui::Response {
        ui.horizontal(|ui| {
            ui.label("time");
            // ui.style_mut().spacing.slider_width = ui.available_width() - 255.0;
            Slider::new(&mut self.frame_idx, 0..=(self.number_of_frames - 1)).ui(ui)
        })
        .response
    }
}

impl MnistApp {
    pub fn input_id(&self) -> InputId {
        self.control.input_id
    }
}
