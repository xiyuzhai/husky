use super::*;
use crate::{item_path::ItemPathPresentation, var_id::VarIdPresentation};
use caryatid::IsCaryatid;
use windlass::Windlass;

impl<TraceProtocol: IsTraceProtocol> TraceSynchrotron<TraceProtocol> {
    pub(crate) fn cache_item_path_presentations(
        &mut self,
        f: impl Fn(ItemPathIdInterface) -> ItemPathPresentation,
    ) {
        for &(item_path_id_interface, _) in self.caryatid.clone().windlasses() {
            if !self
                .item_path_presentations
                .contains_key(&item_path_id_interface)
            {
                self.take_action(TraceSynchrotronAction::CacheItemPathPresentation {
                    item_path_id_interface,
                    item_path_presentation: f(item_path_id_interface),
                })
            }
        }
    }

    pub(crate) fn cache_var_id_presentations_from_caryatid(
        &mut self,
        // return Some if not cache
        f: impl Fn(TraceVarId<TraceProtocol>) -> VarIdPresentation,
    ) {
        for &(item_path_id_interface, windlass) in self.caryatid.clone().windlasses() {
            match windlass {
                Windlass::Specific(var_id) | Windlass::Generic { moored: var_id, .. } => {
                    if !self
                        .var_id_presentations
                        .contains_key(&(item_path_id_interface, var_id))
                    {
                        self.take_action(TraceSynchrotronAction::CacheVarIdPresentation {
                            item_path_id_interface,
                            var_id,
                            var_id_presentation: f(var_id),
                        });
                    }
                }
                _ => (),
            }
        }
    }

    pub(crate) fn cache_var_id_presentations_from_figure(
        &mut self,
        figure: &TraceProtocol::Figure,
        f: impl Fn(TraceVarId<TraceProtocol>) -> VarIdPresentation,
    ) {
        figure.for_all_joint_pedestals(|joint_pedestal| {
            for &(item_path_id_interface, var_id) in &**joint_pedestal {
                if !self
                    .var_id_presentations
                    .contains_key(&(item_path_id_interface, var_id))
                {
                    self.take_action(TraceSynchrotronAction::CacheVarIdPresentation {
                        item_path_id_interface,
                        var_id,
                        var_id_presentation: f(var_id),
                    })
                }
            }
        })
    }
}
