use super::*;
use husky_syn_expr::SynExprIdx;

impl<Task: IsTask> Devtime<Task> {
    pub(crate) fn eager_expr_figure(
        &self,
        expr: SynExprIdx,
        history: &History,
    ) -> SpecificFigureCanvasData {
        todo!()
        // if let Some(entry) = history.get(expr) {
        //     match entry {
        //         HistoryEntry::PureExpr { result, .. } => match result {
        //             Ok(output) => SpecificFigureCanvasData::from_visual_data(
        //                 self.visualize_temp_value(
        //                     output,
        //                     expr.intrinsic_ty(),
        //                     expr.file,
        //                     expr.range,
        //                 )
        //                 .unwrap(),
        //             ),
        //             Err(_) => Default::default(),
        //         },
        //         HistoryEntry::Exec { .. } => todo!(),
        //         HistoryEntry::Loop { .. } => panic!(),
        //         HistoryEntry::ControlFlow { .. } => todo!(),
        //         HistoryEntry::Break => todo!(),
        //         HistoryEntry::PatternMatching { .. } => todo!(),
        //     }
        // } else {
        //     Default::default()
        // }
    }
}