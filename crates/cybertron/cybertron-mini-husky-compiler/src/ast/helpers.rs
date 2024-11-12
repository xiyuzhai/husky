use super::*;
use std::any::Any;

pub fn parent_queries<T>(asts: Seq<Option<Ast>>, ts: Seq<Option<T>>) -> Seq<Option<T>>
where
    T: Any + Send + Sync + Copy,
{
    let parents = asts.map(|ast| ast.map(|ast| ast.parent).flatten());
    ts.index(parents).map(|t| t.flatten())
}
