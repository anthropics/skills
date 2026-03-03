"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
const weekdays = ['SUN', 'MON', 'TUE', 'WED', 'THU', 'FRI', 'SAT'];
/**
 * Only the first parameter is mandatory. Either the second, the third, or both
 * may be left out.
 *
 * If only one parameter is present, the function yeilds a true value on the
 * weekday that the parameter represents. If the string "GMT" is specified as
 * a second parameter, times are taken to be in GMT, otherwise in local timezone.
 *
 * If both wd1 and wd1 are defined, the condition is true if the current weekday
 * is in between those two weekdays. Bounds are inclusive. If the "GMT" parameter
 * is specified, times are taken to be in GMT, otherwise the local timezone is
 * used.
 *
 * Valid "weekday strings" are:
 *
 *     SUN MON TUE WED THU FRI SAT
 *
 * Examples:
 *
 * ``` js
 * weekdayRange("MON", "FRI")
 * true Monday trhough Friday (local timezone).
 *
 * weekdayRange("MON", "FRI", "GMT")
 * same as above, but GMT timezone.
 *
 * weekdayRange("SAT")
 * true on Saturdays local time.
 *
 * weekdayRange("SAT", "GMT")
 * true on Saturdays GMT time.
 *
 * weekdayRange("FRI", "MON")
 * true Friday through Monday (note, order does matter!).
 * ```
 *
 *
 * @param {String} wd1 one of the weekday strings.
 * @param {String} wd2 one of the weekday strings.
 * @param {String} gmt is either the string: GMT or is left out.
 * @return {Boolean}
 */
function weekdayRange(wd1, wd2, gmt) {
    let useGMTzone = false;
    let wd1Index = -1;
    let wd2Index = -1;
    let wd2IsGmt = false;
    if ((0, util_1.isGMT)(gmt)) {
        useGMTzone = true;
    }
    else if ((0, util_1.isGMT)(wd2)) {
        useGMTzone = true;
        wd2IsGmt = true;
    }
    wd1Index = weekdays.indexOf(wd1);
    if (!wd2IsGmt && isWeekday(wd2)) {
        wd2Index = weekdays.indexOf(wd2);
    }
    const todaysDay = getTodaysDay(useGMTzone);
    let result;
    if (wd2Index < 0) {
        result = todaysDay === wd1Index;
    }
    else if (wd1Index <= wd2Index) {
        result = valueInRange(wd1Index, todaysDay, wd2Index);
    }
    else {
        result =
            valueInRange(wd1Index, todaysDay, 6) ||
                valueInRange(0, todaysDay, wd2Index);
    }
    return result;
}
exports.default = weekdayRange;
function getTodaysDay(gmt) {
    return gmt ? new Date().getUTCDay() : new Date().getDay();
}
// start <= value <= finish
function valueInRange(start, value, finish) {
    return start <= value && value <= finish;
}
function isWeekday(v) {
    if (!v)
        return false;
    return weekdays.includes(v);
}
//# sourceMappingURL=weekdayRange.js.map