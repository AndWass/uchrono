use crate::Duration;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/// Represents a point in time of the associated `Clock`.
///
/// TimePoint has generic type `Clock`, serving as a tag type. This ensures that
/// time points from two different clocks cannot be interchanged by accident.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct TimePoint<Clock> {
    since_epoch: Duration,
    _phantom: PhantomData<Clock>,
}

impl<Clock> TimePoint<Clock> {
    /// Create a new [`TimePoint`] with a certain duration since the `Clock` epoch.
    ///
    /// # Examples
    ///
    /// ```
    /// use uchrono::{Duration, TimePoint};
    /// struct MyClock;
    /// TimePoint::<MyClock>::new(Duration::from_seconds(10));
    /// ```
    pub const fn new(since_epoch: Duration) -> Self {
        Self {
            since_epoch,
            _phantom: PhantomData,
        }
    }

    /// Calculate the amount of time elapsed form another instant to this one.
    /// If `earlier` is later than this time point a negative duration is returned.
    ///
    /// # Panics
    ///
    /// Panics if `self.duration_since_epoch() - earlier.duration_since_epoch()` panics.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::{Duration, TimePoint};
    /// struct MyClock;
    /// type MyClockTimePoint = TimePoint<MyClock>;
    /// let first = MyClockTimePoint::new(Duration::from_seconds(10));
    /// let second = MyClockTimePoint::new(Duration::from_millis(12_345));
    /// assert_eq!(second.duration_since(first).millis(), 2345);
    /// ```
    #[inline]
    pub fn duration_since(&self, earlier: Self) -> Duration {
        self.since_epoch - earlier.since_epoch
    }

    /// Calculate the amount of time elapsed form another instant to this one.
    /// If `earlier` is later than this time point a negative duration is returned.
    ///
    /// Returns `None` if `self.duration_since_epoch() - earlier.duration_since_epoch()` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::{Duration, TimePoint};
    /// struct MyClock;
    /// type MyClockTimePoint = TimePoint<MyClock>;
    /// let first = MyClockTimePoint::new(Duration::from_seconds(10));
    /// let second = MyClockTimePoint::new(Duration::from_millis(12_345));
    /// assert_eq!(second.checked_duration_since(first), Some(Duration::from_millis(2345)));
    /// ```
    #[inline]
    pub fn checked_duration_since(&self, earlier: Self) -> Option<Duration> {
        self.since_epoch.checked_sub(earlier.since_epoch)
    }

    /// Get the duration since the epoch
    ///
    /// ```
    /// use uchrono::{Duration, TimePoint};
    /// struct MyClock;
    /// assert_eq!(TimePoint::<MyClock>::new(Duration::from_seconds(10)).duration_since_epoch(), Duration::from_seconds(10));
    /// ```
    #[inline]
    pub fn duration_since_epoch(&self) -> Duration {
        self.since_epoch
    }
}

impl<Clock> Add<Duration> for TimePoint<Clock> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Duration) -> Self::Output {
        self.since_epoch += rhs;
        self
    }
}

impl<Clock> AddAssign<Duration> for TimePoint<Clock> {
    #[inline]
    fn add_assign(&mut self, rhs: Duration) {
        self.since_epoch += rhs;
    }
}

impl<Clock> Sub<Self> for TimePoint<Clock> {
    type Output = Duration;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.duration_since(rhs)
    }
}

impl<Clock> Sub<Duration> for TimePoint<Clock> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Duration) -> Self::Output {
        self.since_epoch -= rhs;
        self
    }
}

impl<Clock> SubAssign<Duration> for TimePoint<Clock> {
    #[inline]
    fn sub_assign(&mut self, rhs: Duration) {
        self.since_epoch -= rhs;
    }
}

#[cfg(test)]
mod tests {
    use crate::{Duration, TimePoint};

    #[test]
    #[should_panic]
    fn duration_since() {
        struct C;
        let later: TimePoint<C> = TimePoint::new(Duration::from_micros(-2));
        let earlier = TimePoint::new(Duration::MAX);
        let _ = later.duration_since(earlier);
    }
}
