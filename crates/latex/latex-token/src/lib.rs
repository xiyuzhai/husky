#![feature(if_let_guard)]
#![feature(step_trait)]
pub mod idx;
pub mod lane;
pub mod lexer;
pub mod reserved_char;
pub mod storage;
pub mod stream;
#[cfg(test)]
mod tests;
pub mod token;

use self::storage::LxTokenStorage;
#[cfg(test)]
use self::tests::*;
use latex_prelude::mode::LxMode;
