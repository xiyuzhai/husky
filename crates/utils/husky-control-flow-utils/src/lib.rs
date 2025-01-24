#[macro_export]
macro_rules! loop_require {
    ($condition: expr) => {
        if !$condition {
            continue;
        }
    };
}

#[macro_export]
macro_rules! require {
    ($condition: expr) => {
        if !$condition {
            return Default::default();
        }
    };
    ($condition: expr, $result: expr) => {
        if !$condition {
            return $result;
        }
    };
    (let $pattern: pat = $expr: expr) => {
        let $pattern = $expr else {
            return Default::default();
        };
    };
    (let $pattern: pat = $expr: expr, $result: expr) => {
        let $pattern = $expr else {
            return $result;
        };
    };
}

pub use require as rq;

#[macro_export]
macro_rules! pass {
    ($note: expr) => {
        ()
    };
}
