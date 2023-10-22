//! Traits and clock implementation of various clocks
//!
//! The [`Clock`] trait represents a clock that can fetch the current
//! time using that clock.
use crate::{Duration, TimePoint};

/// Trait for clocks that can provide the current time.
pub trait Clock: Sized {
    /// Get the current time from a clock.
    fn now(&self) -> TimePoint<Self>;

    /// Construct a new time point in this clock domain. This is a shorthand for
    /// `TimePoint::<SomeClock>::new(since_epoch)`.
    #[inline(always)]
    fn time_point(since_epoch: Duration) -> TimePoint<Self> {
        TimePoint::new(since_epoch)
    }
}

#[cfg(feature = "std")]
mod std_mod
{
    use lazy_static::lazy_static;
    use super::*;

    /// A clock backed by `std::time::Instant::now()`.
    ///
    /// Only available with the `std` feature.
    pub struct InstantClock;

    impl Clock for InstantClock {
        fn now(&self) -> TimePoint<Self> {
            lazy_static! {
                static ref EPOCH: std::time::Instant = std::time::Instant::now();
            }

            let since_epoch = std::time::Instant::now().saturating_duration_since(*EPOCH);
            TimePoint::<Self>::new(Duration::from_micros(since_epoch.as_micros() as i64))
        }
    }

    /// A clock backed by `std::time::SystemTime::now()`.
    ///
    /// Only available with the `std` feature.
    pub struct SystemClock;

    impl Clock for SystemClock {
        fn now(&self) -> TimePoint<Self> {
            let n = std::time::SystemTime::now();
            let since_epoch = n.duration_since(std::time::SystemTime::UNIX_EPOCH).unwrap();
            TimePoint::<Self>::new(Duration::from_micros(since_epoch.as_micros() as i64))
        }
    }
}

#[cfg(feature = "std")]
pub use std_mod::*;
