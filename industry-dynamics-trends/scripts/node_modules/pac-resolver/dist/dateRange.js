"use strict";
/**
 * If only a single value is specified (from each category: day, month, year), the
 * function returns a true value only on days that match that specification. If
 * both values are specified, the result is true between those times, including
 * bounds.
 *
 * Even though the examples don't show, the "GMT" parameter can be specified
 * in any of the 9 different call profiles, always as the last parameter.
 *
 * Examples:
 *
 * ``` js
 * dateRange(1)
 * true on the first day of each month, local timezone.
 *
 * dateRange(1, "GMT")
 * true on the first day of each month, GMT timezone.
 *
 * dateRange(1, 15)
 * true on the first half of each month.
 *
 * dateRange(24, "DEC")
 * true on 24th of December each year.
 *
 * dateRange(24, "DEC", 1995)
 * true on 24th of December, 1995.
 *
 * dateRange("JAN", "MAR")
 * true on the first quarter of the year.
 *
 * dateRange(1, "JUN", 15, "AUG")
 * true from June 1st until August 15th, each year (including June 1st and August
 * 15th).
 *
 * dateRange(1, "JUN", 15, 1995, "AUG", 1995)
 * true from June 1st, 1995, until August 15th, same year.
 *
 * dateRange("OCT", 1995, "MAR", 1996)
 * true from October 1995 until March 1996 (including the entire month of October
 * 1995 and March 1996).
 *
 * dateRange(1995)
 * true during the entire year 1995.
 *
 * dateRange(1995, 1997)
 * true from beginning of year 1995 until the end of year 1997.
 * ```
 *
 * dateRange(day)
 * dateRange(day1, day2)
 * dateRange(mon)
 * dateRange(month1, month2)
 * dateRange(year)
 * dateRange(year1, year2)
 * dateRange(day1, month1, day2, month2)
 * dateRange(month1, year1, month2, year2)
 * dateRange(day1, month1, year1, day2, month2, year2)
 * dateRange(day1, month1, year1, day2, month2, year2, gmt)
 *
 * @param {String} day is the day of month between 1 and 31 (as an integer).
 * @param {String} month is one of the month strings: JAN FEB MAR APR MAY JUN JUL AUG SEP OCT NOV DEC
 * @param {String} year is the full year number, for example 1995 (but not 95). Integer.
 * @param {String} gmt is either the string "GMT", which makes time comparison occur in GMT timezone; if left unspecified, times are taken to be in the local timezone.
 * @return {Boolean}
 */
Object.defineProperty(exports, "__esModule", { value: true });
function dateRange() {
    // TODO: implement me!
    return false;
}
exports.default = dateRange;
//# sourceMappingURL=dateRange.js.map