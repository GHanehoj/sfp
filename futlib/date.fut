-- A simple date library.  Inspired by code from LexiFi.
--
-- This library does not handle any ancient calendars or anything like
-- that.  It's designed for simplicty (and therefore speed).

-- The implementation is by a module which is immediately opened.  The
-- intent is to make the type of dates abstract.  When Futhark gets
-- separate interface files (or some other such mechanism), this
-- should go away.

module type date = {
  type date

  -- Add days to date.
  val add_days: date -> i32 -> date
  -- Subtract days from date.
  val sub_days: date -> i32 -> date

  -- The time from the first date to the second, in fractions of a
  -- 365-day year.
  val diff_dates: date -> date -> f64

  -- Convert a date to a triple of (year,month,day).  Months and days
  -- are 1-indexed.  The time is assumed to be 12:00 that day.
  val triple_of_date: date -> (i32,i32,i32)

  -- The inverse of 'triple_of_date'.  The result is undefined if the
  -- triple does not describe a valid date.
  val date_of_triple: (i32,i32,i32) -> date

  -- True if the given triple encodes a valid (year,month,day)-date.
  val check_date: (i32,i32,i32) -> bool

  val same_date: date -> date -> bool
}

open ({
  type date = i32

  type gregorian = { year: i32,
                     month: i32,
                     day: i32,
                     hour: i32,
                     minute: i32 }

  val hours_in_day = 24
  val minutes_in_day = hours_in_day * 60
  val fminutes_in_day = f64 minutes_in_day
  val minutes_to_noon = (hours_in_day / 2) * 60

  -- Communications of the ACM by Henry F. Fliegel and Thomas C. Van Flandern,
  -- ``A Machine Algorithm for Processing Calendar Dates'',
  -- CACM, volume 11, number 10, October 1968, p. 657
  fun date_of_gregorian ({year = y, month = m, day = d, hour = hr, minute = mn}: gregorian) =
    ((if m == 1 || m == 2 then
       (1461 * (y + 4800 - 1)) / 4 +
        (367 * (m + 10)) / 12 -
        (3 * ((y + 4900 - 1) / 100)) / 4
      else
       (1461 * (y + 4800)) / 4 +
         (367 * (m - 2)) / 12 -
         (3 * ((y + 4900) / 100)) / 4) + d - 32075 - 2444238) * minutes_in_day
    + hr * 60 + mn

  fun gregorian_of_date (minutes_since_epoch: i32) =
    let jul = minutes_since_epoch / minutes_in_day
    let l = jul + 68569 + 2444238
    let n = (4 * l) / 146097
    let l = l - (146097 * n + 3) / 4
    let i = (4000 * (l + 1)) / 1461001
    let l = l - (1461 * i) / 4 + 31
    let j = (80 * l) / 2447
    let d = l - (2447 * j) / 80
    let l = j / 11
    let m = j + 2 - (12 * l)
    let y = 100 * (n - 49) + i + l
    let daytime = minutes_since_epoch % minutes_in_day
    in if daytime == minutes_to_noon
       then {year = y, month = m, day = d, hour = 12, minute = 0}
       else {year = y, month = m, day = d, hour = daytime / 60, minute = daytime % 60}

  fun check_date ((year,month,day): (i32,i32,i32)) =
    1 <= day &&
    1 <= month && month <= 12 &&
    (day <= 28 ||
     if month == 2 then
     day == 29 && year % 4 == 0 && ((year % 400 == 0) || (year % 100 != 0))
     else if month == 4 || month == 6 || month == 9 || month == 11
     then day <= 30
     else day <= 31)

  fun date_of_triple (year: i32, month: i32, day: i32) =
    date_of_gregorian {year=year, month=month, day=day, hour=12, minute=0}

  fun triple_of_date (x: date) =
    let {year, month, day, hour = _, minute = _} = gregorian_of_date x
    in (year, month, day)

  fun int_of_date (x: date) = x
  fun date_of_int (x: i32) = x

  val fminutes_in_365 = f64 (minutes_in_day * 365)
  val inv_fminutes_in_365 = 1.0 / fminutes_in_365
  val inv_fminutes_in_day = 1.0 / fminutes_in_day

  fun add_act_365 (t: date) (dt: f64) =
    date_of_int (i32 (f64 (int_of_date t) + fminutes_in_365 * dt))
  fun add_days (t1: date) (displ: i32) =
    date_of_int(int_of_date t1 + displ * minutes_in_day)
  fun sub_days (t1: date) (displ: i32) =
    add_days t1 (-displ)
  fun days_between (t1: date) (t2: date) =
    (f64 (int_of_date t2 - int_of_date t1)) * inv_fminutes_in_day
  fun diff_dates (t1: date) (t2: date) =
    days_between t1 t2 / 365.0

  fun same_date (x: date) (y: date) = x == y

} : date)
