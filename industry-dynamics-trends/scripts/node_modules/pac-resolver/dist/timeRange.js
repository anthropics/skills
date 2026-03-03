"use strict";
/**
 * True during (or between) the specified time(s).
 *
 * Even though the examples don't show it, this parameter may be present in
 * each of the different parameter profiles, always as the last parameter.
 *
 *
 * Examples:
 *
 * ``` js
 * timerange(12)
 * true from noon to 1pm.
 *
 * timerange(12, 13)
 * same as above.
 *
 * timerange(12, "GMT")
 * true from noon to 1pm, in GMT timezone.
 *
 * timerange(9, 17)
 * true from 9am to 5pm.
 *
 * timerange(8, 30, 17, 00)
 * true from 8:30am to 5:00pm.
 *
 * timerange(0, 0, 0, 0, 0, 30)
 * true between midnight and 30 seconds past midnight.
 * ```
 *
 * timeRange(hour)
 * timeRange(hour1, hour2)
 * timeRange(hour1, min1, hour2, min2)
 * timeRange(hour1, min1, sec1, hour2, min2, sec2)
 * timeRange(hour1, min1, sec1, hour2, min2, sec2, gmt)
 *
 * @param {String} hour is the hour from 0 to 23. (0 is midnight, 23 is 11 pm.)
 * @param {String} min minutes from 0 to 59.
 * @param {String} sec seconds from 0 to 59.
 * @param {String} gmt either the string "GMT" for GMT timezone, or not specified, for local timezone.
 * @return {Boolean}
 */
Object.defineProperty(exports, "__esModule", { value: true });
function timeRange() {
    // eslint-disable-next-line prefer-rest-params
    const args = Array.prototype.slice.call(arguments);
    const lastArg = args.pop();
    const useGMTzone = lastArg === 'GMT';
    const currentDate = new Date();
    if (!useGMTzone) {
        args.push(lastArg);
    }
    let result = false;
    const noOfArgs = args.length;
    const numericArgs = args.map((n) => parseInt(n, 10));
    // timeRange(hour)
    if (noOfArgs === 1) {
        result = getCurrentHour(useGMTzone, currentDate) === numericArgs[0];
        // timeRange(hour1, hour2)
    }
    else if (noOfArgs === 2) {
        const currentHour = getCurrentHour(useGMTzone, currentDate);
        result = numericArgs[0] <= currentHour && currentHour < numericArgs[1];
        // timeRange(hour1, min1, hour2, min2)
    }
    else if (noOfArgs === 4) {
        result = valueInRange(secondsElapsedToday(numericArgs[0], numericArgs[1], 0), secondsElapsedToday(getCurrentHour(useGMTzone, currentDate), getCurrentMinute(useGMTzone, currentDate), 0), secondsElapsedToday(numericArgs[2], numericArgs[3], 59));
        // timeRange(hour1, min1, sec1, hour2, min2, sec2)
    }
    else if (noOfArgs === 6) {
        result = valueInRange(secondsElapsedToday(numericArgs[0], numericArgs[1], numericArgs[2]), secondsElapsedToday(getCurrentHour(useGMTzone, currentDate), getCurrentMinute(useGMTzone, currentDate), getCurrentSecond(useGMTzone, currentDate)), secondsElapsedToday(numericArgs[3], numericArgs[4], numericArgs[5]));
    }
    return result;
}
exports.default = timeRange;
function secondsElapsedToday(hh, mm, ss) {
    return hh * 3600 + mm * 60 + ss;
}
function getCurrentHour(gmt, currentDate) {
    return gmt ? currentDate.getUTCHours() : currentDate.getHours();
}
function getCurrentMinute(gmt, currentDate) {
    return gmt ? currentDate.getUTCMinutes() : currentDate.getMinutes();
}
function getCurrentSecond(gmt, currentDate) {
    return gmt ? currentDate.getUTCSeconds() : currentDate.getSeconds();
}
// start <= value <= finish
function valueInRange(start, value, finish) {
    return start <= value && value <= finish;
}
//# sourceMappingURL=timeRange.js.map