#![allow(non_camel_case_types)]
mod file;
mod position;

use crate::{file::FileId, position::PositionIdx};
use husky_core::*;
use husky_standard_linket_impl::ugly::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenFilePosition {
    file: FileId,
    position: PositionIdx,
}

impl From<__VarId> for TokenFilePosition {
    fn from(id: __VarId) -> Self {
        match id {
            __VarId::Pair([file, position]) => Self {
                file: FileId::new(file),
                position: PositionIdx::new(position),
            },
            _ => unreachable!(),
        }
    }
}

impl Into<__VarId> for TokenFilePosition {
    fn into(self) -> __VarId {
        __VarId::Pair([self.file.into(), self.position.into()])
    }
}

thread_local! {
    static TOKEN_FILE_POSITION: std::cell::Cell<Option<TokenFilePosition>> = Default::default();
}

fn replace_file_position(id: TokenFilePosition) -> Option<TokenFilePosition> {
    TOKEN_FILE_POSITION.replace(Some(id))
}

fn set_file_position(id: Option<TokenFilePosition>) {
    TOKEN_FILE_POSITION.set(id)
}

pub struct TOKEN_FILE_POSITION {}

#[allow(non_upper_case_globals)]
pub static mut __TOKEN_FILE_POSITION__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

impl __IsStaticVar<__VarId> for TOKEN_FILE_POSITION {
    fn item_path_id_interface() -> __ItemPathIdInterface {
        unsafe {
            __TOKEN_FILE_POSITION__ITEM_PATH_ID_INTERFACE
                .expect("__TOKEN_FILE_POSITION__ITEM_PATH_ID_INTERFACE")
        }
    }

    fn page_var_ids_aux(locked: &[__ItemPathIdInterface]) -> impl Iterator<Item = __VarId> {
        [todo!()].into_iter()
    }

    fn default_page_start(
        figure_zone: __FigureZone,
        locked: &[__ItemPathIdInterface],
    ) -> husky_linket_impl::static_var::StaticVarResult<__VarId, __VarId> {
        todo!()
    }

    fn get_id() -> __VarId {
        TOKEN_FILE_POSITION.get().unwrap().into()
    }

    fn try_set_var_id_aux(
        id: __VarId,
        locked: &[__ItemPathIdInterface],
    ) -> husky_linket_impl::static_var::StaticVarResult<__VarId, impl FnOnce() + 'static> {
        let old = replace_file_position(id.into());
        Ok(move || {
            set_file_position(old);
        })
    }

    fn try_set_default_var_id(
        locked: &[__ItemPathIdInterface],
    ) -> husky_linket_impl::static_var::StaticVarResult<__VarId, (__VarId, impl FnOnce() + 'static)>
    {
        let default = [0, 0].into();
        Ok((default, Self::try_set_var_id(default, locked)?))
    }

    type Value = __Value;

    fn get_value() -> Self::Value {
        todo!()
    }

    fn zones() -> &'static [__FigureZone] {
        &[__FigureZone::Text]
    }
}
