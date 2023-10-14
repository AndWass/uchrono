use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use lazy_static::lazy_static;

/// Represent a duration of time in microseconds
///
/// ## Overflow / Underflow behaviour
///
/// Any over or underflow will cause a panic.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct Duration
{
    micros: i64,
}

impl Duration {
    pub const ZERO: Duration = Duration { micros: 0 };
    /// Create a new [`Duration`] from `micros` microseconds.
    ///
    /// # Arguments
    ///
    /// * `micros`: Number of microseconds for this duration.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur: Duration = Duration::from_micros(1234);
    /// ```
    #[inline]
    pub const fn from_micros(micros: i64) -> Self {
        Self {
            micros
        }
    }

    /// Create a new [`Duration`] from milliseconds.
    ///
    /// # Arguments
    ///
    /// * `millis`: Number of milliseconds
    ///
    /// # Panics
    ///
    /// Panics if `millis*1000` causes overflow of `i64`
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_millis(10);
    /// assert_eq!(dur, Duration::from_micros(10_000));
    /// ```
    #[inline]
    pub fn from_millis(millis: i64) -> Self {
        Self::from_micros(millis.checked_mul(1000).expect("Overflow converting from milliseconds to Duration"))
    }

    /// Create a new [`Duration`] from seconds.
    ///
    /// # Arguments
    ///
    /// * `seconds`: Number of seconds.
    ///
    /// # Panics
    ///
    /// Panics if `seconds*1_000_000` causes overflow of `i64`
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_seconds(10);
    /// assert_eq!(dur, Duration::from_micros(10_000_000));
    /// ```
    #[inline]
    pub fn from_seconds(seconds: i64) -> Self {
        Self::from_micros(seconds.checked_mul(1_000_000).expect("Overflow converting from seconds to Duration"))
    }

    /// Get the number of microseconds this Duration represents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_micros(10);
    /// assert_eq!(dur.micros(), 10);
    /// ```
    #[inline]
    pub const fn micros(&self) -> i64 {
        self.micros
    }

    /// Get the number of milliseconds, rounded towards 0.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_micros(10_123);
    /// assert_eq!(dur.millis(), 10);
    /// ```
    #[inline]
    pub const fn millis(&self) -> i64 {
        self.micros / 1000
    }

    /// Get the number of seconds, rounded towards 0.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_micros(10_123_456);
    /// assert_eq!(dur.seconds(), 10);
    /// ```
    #[inline]
    pub const fn seconds(&self) -> i64 {
        self.micros / 1_000_000
    }

    /// Get the fractional portion of a second.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// let dur = Duration::from_micros(10_123_456);
    /// assert_eq!(dur.seconds(), 10);
    /// assert_eq!(dur.subsec_micros(), 123_456);
    /// ```
    #[inline]
    pub const fn subsec_micros(&self) -> i32 {
        (self.micros % 1_000_000) as i32
    }


    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.micros.checked_add(rhs.micros).map(Self::from_micros)
    }

    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.micros.checked_sub(rhs.micros).map(Self::from_micros)
    }
}

impl Add for Duration
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs).expect("Overflow when adding durations")
    }
}

impl AddAssign for Duration {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for Duration {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs).expect("Underflow when subtracting durations")
    }
}

impl SubAssign for Duration {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct TimePoint<Tag>
{
    since_epoch: Duration,
    _phantom: PhantomData<Tag>
}

impl<T> TimePoint<T> {
    pub const fn new(since_epoch: Duration) -> Self {
        Self {
            since_epoch,
            _phantom: PhantomData
        }
    }

    /// Calculate the amount of time elapsed form another instant to this one.
    /// If `earlier` is later than this one a negaive duration is returned.
    ///
    /// # Panics
    ///
    /// Panics if `self.duration_since_epoch() - earlier.duration_since_epoch()` panics.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::{Duration, GenericTimePoint};
    /// let first = GenericTimePoint::new(Duration::from_seconds(10));
    /// let second = GenericTimePoint::new(Duration::from_millis(12_345));
    /// assert_eq!(second.duration_since(first).millis(), 2345);
    /// ```
    #[inline]
    pub fn duration_since(&self, earlier: Self) -> Duration {
        self.since_epoch - earlier.since_epoch
    }

    #[inline]
    pub fn duration_since_epoch(&self) -> Duration {
        self.since_epoch
    }
}

impl<T: Now> TimePoint<T> {
    #[inline(always)]
    pub fn now() -> Self {
        T::now()
    }
}

impl<T> Add<Duration> for TimePoint<T> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Duration) -> Self::Output {
        self.since_epoch += rhs;
        self
    }
}

impl<T> AddAssign<Duration> for TimePoint<T> {
    #[inline]
    fn add_assign(&mut self, rhs: Duration) {
        self.since_epoch += rhs;
    }
}

impl<T> Sub<Self> for TimePoint<T> {
    type Output = Duration;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.duration_since(rhs)
    }
}

impl<T> Sub<Duration> for TimePoint<T> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Duration) -> Self::Output {
        self.since_epoch -= rhs;
        self
    }
}

impl<T> SubAssign<Duration> for TimePoint<T> {
    #[inline]
    fn sub_assign(&mut self, rhs: Duration) {
        self.since_epoch -= rhs;
    }
}

pub trait Now: Sized {
    fn now() -> TimePoint<Self>;
}

pub struct MonotonicClock;

impl Now for MonotonicClock {
    fn now() -> TimePoint<Self> {
        lazy_static! {
            static ref EPOCH: std::time::Instant = std::time::Instant::now();
        }

        let since_epoch = std::time::Instant::now().saturating_duration_since(*EPOCH);
        TimePoint::<Self>::new(Duration::from_micros(since_epoch.as_micros() as i64))
    }
}
pub struct SystemClock;

impl Now for SystemClock {
    fn now() -> TimePoint<Self> {
        let n = std::time::SystemTime::now();
        let since_epoch = n.duration_since(std::time::SystemTime::UNIX_EPOCH).unwrap();
        TimePoint::<Self>::new(Duration::from_micros(since_epoch.as_micros() as i64))
    }
}

pub struct GenericClock;

pub type MonotonicTimePoint = TimePoint<MonotonicClock>;
pub type SystemTimePoint = TimePoint<SystemClock>;
pub type GenericTimePoint = TimePoint<GenericClock>;

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