//! A time point and duration library.
//!
//! # Duration
//!
//! The [`Duration`] type is inspired by [`smoltcp::time::Duration`] and
//! [`embassy_time::Duration`] but allows for negative duration values as well.
//!
//! [`smoltcp::time::Duration`]: https://docs.rs/smoltcp/0.10.0/smoltcp/time/struct.Duration.html
//! [`embassy_time::Duration`]: https://docs.embassy.dev/embassy-time/git/default/struct.Duration.html
//!
//! # Time points
//!
//! The [`TimePoint`] type is keyed on which `Clock` it originates from. This catches errors such
//! as accidentally comparing time points from different clocks.
//!
//! # Features
//!
//!   * `std` - enabled by default.
//! 

#![cfg_attr(not(feature = "std"), no_std)]

mod duration;
mod timepoint;

pub mod clock;

pub use duration::Duration;
pub use timepoint::TimePoint;

#[cfg(test)]
mod tests
{
    use crate::Duration;

    #[test]
    fn negative_duration() {
        let dur = Duration::from_micros(-1234);
        assert_eq!(dur.millis(), -1);
    }

    #[test]
    fn subsecond_micros() {
        let dur = Duration::from_micros(1_234_567);
        assert_eq!(dur.subsec_micros(), 234_567);
        let dur = Duration::from_micros(i64::MAX);
        assert_eq!(dur.subsec_micros(), 775807);

        let dur = Duration::from_micros(i64::MIN);
        assert_eq!(dur.subsec_micros(), -775808);
    }
}