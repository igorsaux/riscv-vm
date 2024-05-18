#[cfg(not(feature = "tracy"))]
mod fallback;
#[cfg(feature = "tracy")]
mod tracy;

#[cfg(not(feature = "tracy"))]
pub use fallback::{non_continuous_frame, plot, span, frame_mark};
#[cfg(feature = "tracy")]
pub use tracy_client::{non_continuous_frame, plot, span, frame_mark};

pub use tracing::instrument;
