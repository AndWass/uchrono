use core::ops::{Add, AddAssign, Sub, SubAssign};

/// Represent a duration of time in microseconds
///
/// # Overflow / Underflow behaviour
///
/// Any over or underflow will cause a panic.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct Duration {
    micros: i64,
}

impl Duration {
    /// Constant always equals to `Duration::from_micros(0)`
    pub const ZERO: Duration = Duration { micros: 0 };
    /// Constant always equals to `Duration::from_micros(i64::MAX)`
    pub const MAX: Duration = Duration { micros: i64::MAX };
    /// Constant always equals to `Duration::from_micros(i64::MIN)`
    pub const MIN: Duration = Duration { micros: i64::MIN };
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
        Self { micros }
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
        Self::from_micros(
            millis
                .checked_mul(1000)
                .expect("Overflow converting from milliseconds to Duration"),
        )
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
        Self::from_micros(
            seconds
                .checked_mul(1_000_000)
                .expect("Overflow converting from seconds to Duration"),
        )
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

    /// Checked [`Duration`] addition. Returning `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// assert_eq!(Duration::from_micros(i64::MAX - 2).checked_add(Duration::from_micros(1)), Some(Duration::from_micros(i64::MAX-1)));
    /// assert_eq!(Duration::from_micros(i64::MAX - 2).checked_add(Duration::from_micros(3)), None);
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.micros.checked_add(rhs.micros).map(Self::from_micros)
    }

    /// Checked [`Duration`] subtraction. Returning `None` if underflow occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// assert_eq!(Duration::from_micros(i64::MIN + 2).checked_sub(Duration::from_micros(1)), Some(Duration::from_micros(i64::MIN+1)));
    /// assert_eq!(Duration::from_micros(i64::MIN + 2).checked_sub(Duration::from_micros(3)), None);
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.micros.checked_sub(rhs.micros).map(Self::from_micros)
    }

    /// Saturating [`Duration`] addition, saturating at the bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// assert_eq!(Duration::from_micros(i64::MAX - 2).saturating_add(Duration::from_micros(1)), Duration::from_micros(i64::MAX-1));
    /// assert_eq!(Duration::from_micros(i64::MAX - 2).saturating_add(Duration::from_micros(3)), Duration::from_micros(i64::MAX));
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        Self::from_micros(self.micros.saturating_add(rhs.micros))
    }

    /// Saturating [`Duration`] subtraction, saturating at the bounds instead of underflowing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use uchrono::Duration;
    /// assert_eq!(Duration::from_micros(i64::MIN + 2).saturating_sub(Duration::from_micros(1)), Duration::from_micros(i64::MIN+1));
    /// assert_eq!(Duration::from_micros(i64::MIN + 2).saturating_sub(Duration::from_micros(3)), Duration::from_micros(i64::MIN));
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        Self::from_micros(self.micros.saturating_sub(rhs.micros))
    }
}

/// Uses [`Duration::checked_add`]
///
/// # Panics
///
/// Panics when [`Duration::checked_add`] returns `None`.
impl Add for Duration {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
            .expect("Overflow when adding durations")
    }
}

/// Uses [`Add::add`]
///
/// # Panics
///
/// Panics when [`Add::add`] panics.
impl AddAssign for Duration {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

/// Uses [`Duration::checked_sub`]
///
/// # Panics
///
/// Panics when [`Duration::checked_sub`] returns `None`
impl Sub for Duration {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("Underflow when subtracting durations")
    }
}

/// Uses [`Sub::sub`]
///
/// # Panics
///
/// Panics when [`Sub::sub`] panics.
impl SubAssign for Duration {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn from_millis() {
        let _ = Duration::from_millis(i64::MAX);
    }

    #[test]
    #[should_panic]
    fn from_seconds() {
        let _ = Duration::from_seconds(i64::MAX);
    }

    #[test]
    #[should_panic]
    fn add() {
        let lhs = Duration::MAX;
        let rhs = Duration::from_micros(1);
        let _ = lhs + rhs;
    }

    #[test]
    #[should_panic]
    fn add_assign() {
        let mut lhs = Duration::MAX;
        let rhs = Duration::from_micros(1);
        lhs += rhs;
    }

    #[test]
    #[should_panic]
    fn sub() {
        let lhs = Duration::MIN;
        let rhs = Duration::from_micros(1);
        let _ = lhs - rhs;
    }

    #[test]
    #[should_panic]
    fn sub_assign() {
        let mut lhs = Duration::MIN;
        let rhs = Duration::from_micros(1);
        lhs -= rhs;
    }
}
