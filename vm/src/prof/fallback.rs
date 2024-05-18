#[macro_export]
macro_rules! non_continuous_frame {
    ($name:literal) => {
        ()
    };
}

#[macro_export]
macro_rules! plot {
    ($name: expr, $value: expr) => {
        ()
    };
}

#[macro_export]
macro_rules! span {
    () => {};
    ($name: expr) => {
        ()
    };
    ($name: expr, $callstack_depth: expr) => {
        ()
    };
}

#[inline(always)]
pub fn frame_mark() {}

pub use non_continuous_frame;
pub use plot;
pub use span;
