 A no_std compatible time point and duration library.

 # Duration

 The `Duration` type is inspired by [`smoltcp::time::Duration`] and
 [`embassy_time::Duration`] but allows for negative duration values as well.

 [`smoltcp::time::Duration`]: https://docs.rs/smoltcp/0.10.0/smoltcp/time/struct.Duration.html
 [`embassy_time::Duration`]: https://docs.embassy.dev/embassy-time/git/default/struct.Duration.html

 # Time points

 The `TimePoint` type is keyed on which `Clock` it originates from. This catches errors such
 as accidentally comparing time points from different clocks.

 # Features

   * `std` - enabled by default.
