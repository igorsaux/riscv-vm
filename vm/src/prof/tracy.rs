#[global_allocator]
static GLOBAL: tracy_client::ProfiledAllocator<std::alloc::System> =
    tracy_client::ProfiledAllocator::new(std::alloc::System, 128);

pub use tracy_client::non_continuous_frame;
pub use tracy_client::plot;
pub use tracy_client::span;
pub use tracy_client::frame_mark;
