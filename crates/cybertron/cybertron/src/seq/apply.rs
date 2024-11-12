use super::{idx::Idx, *};
use husky_decl_macro_utils::for_all_non_unit_tuple_tys;
use paste::paste;
use std::any::Any;

macro_rules! impl_apply {
    ($i: literal, $($t: ident),*) => {
        paste!{
            pub trait  [<Apply $i>] <$($t,)* R>
            where
                $($t: Any + Send + Sync,)*
                R: Any + Send + Sync,
            {
                fn apply(self, $([< $t:snake >]: Seq<$t>),*) -> Seq<R>;
            }

            impl<$($t),*, R, F> [<Apply $i>]<$($t,)* R> for F
            where
                $($t: Any + Send + Sync + Copy,)*
                R: Any + Send + Sync,
                F: Fn($($t,)*) -> R,
            {
                fn apply(self, $([< $t:snake >]: Seq<$t>),*) -> Seq<R> {
                    $(let [< $t:snake _data >] = [< $t:snake >].data();)*
                    let len = t1_data.len();
                    $(assert_eq!([< $t:snake _data >].len(), len);)*
                    let result: Vec<_> = (0..len)
                                .into_iter()
                                .map(|i| self($([< $t:snake _data >][i]),*))
                                .collect();
                    Seq::new(result)
                }
            }
        }
    };
}

for_all_non_unit_tuple_tys! {numbered impl_apply}

macro_rules! impl_apply_enumerated {
    ($i: literal, $($t: ident),*) => {
        paste!{
            pub trait  [<ApplyEnumerated $i>] <$($t,)* R>
            where
                $($t: Any + Send + Sync,)*
                R: Any + Send + Sync,
            {
                fn apply_enumerated(self, $([< $t:snake >]: Seq<$t>),*) -> Seq<R>;
            }

            impl<$($t),*, R, F> [<ApplyEnumerated $i>]<$($t,)* R> for F
            where
                $($t: Any + Send + Sync + Copy,)*
                R: Any + Send + Sync,
                F: Fn(Idx, $($t,)*) -> R,
            {
                fn apply_enumerated(self, $([< $t:snake >]: Seq<$t>),*) -> Seq<R> {
                    $(let [< $t:snake _data >] = [< $t:snake >].data();)*
                    let len = t1_data.len();
                    $(assert_eq!([< $t:snake _data >].len(), len);)*
                    let result: Vec<_> = (0..len)
                                .into_iter()
                                .map(|i| self(idx!(i), $([< $t:snake _data >][i]),*))
                                .collect();
                    Seq::new(result)
                }
            }
        }
    };
}

for_all_non_unit_tuple_tys! {numbered impl_apply_enumerated}

impl<T> Seq<T>
where
    T: Send + Sync + Copy + Eq + 'static,
{
    pub fn pair<S>(self, other: Seq<S>) -> Seq<(T, S)>
    where
        S: Send + Sync + Copy + Eq + 'static,
    {
        (|t, s| (t, s)).apply(self, other)
    }
}
