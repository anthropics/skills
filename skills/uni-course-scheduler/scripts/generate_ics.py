#!/usr/bin/env python3
"""Generate an ICS calendar from a course-planner plan JSON.

Design decisions (reuse for any university):
- One VEVENT per session per teaching week (no RRULE+EXDATE: EXDATE does not
  shift an RRULE COUNT, so explicit occurrences are the predictable way to
  exclude break/flexibility weeks).
- TZID from meta.timezone with a VTIMEZONE component (DST-safe).
- 15-minute VALARM reminders on every event.
- Reads meta.semester_start (YYYY-MM-DD, Monday), meta.num_teaching_weeks,
  meta.excluded_weeks (1-based week numbers with no classes, e.g. mid-sem
  break) and meta.timezone.

Usage:
    python3 generate_ics.py <plan.json> [output.ics]
"""
import json
import sys
from datetime import datetime, date, timedelta, timezone

from icalendar import (Calendar, Event, Alarm, vText, vDatetime, vDuration,
                       Timezone, TimezoneStandard, TimezoneDaylight)

INPUT = sys.argv[1] if len(sys.argv) > 1 else "plan.json"
OUTPUT = sys.argv[2] if len(sys.argv) > 2 else "course_schedule.ics"

with open(INPUT, "r", encoding="utf-8") as f:
    data = json.load(f)

meta = data["meta"]

# Data source: prefer cloud stp_icsgen output (combined["ics"]), else fall back
# to weekly_schedule (local mode). This keeps existing behavior while enabling
# cloud-driven ICS generation.
ico = data.get("ics") or {}
if ico and ico.get("events"):
    schedule = ico["events"]
    # cloud provides meta overrides
    meta = {**meta, **ico.get("meta", {})}
else:
    schedule = data["weekly_schedule"]["schedule"]

WEEK1_MONDAY = date.fromisoformat(meta["semester_start"])
NUM_WEEKS = int(meta.get("num_teaching_weeks", 13))
EXCLUDED_WEEKS = [int(w) for w in meta.get("excluded_weeks", [])]
TIMEZONE_ID = meta.get("timezone", "Australia/Sydney")

def teaching_week_monday(w):
    """Monday of teaching week w (1-based). EXCLUDED_WEEKS holds 1-based
    calendar slot numbers (from semester_start) with no classes, e.g. the
    mid-sem break at slot 6. Teaching week w maps to calendar slot
    w + (excluded slots <= w), so weeks after the break shift forward."""
    slot = w + sum(1 for e in EXCLUDED_WEEKS if e <= w)
    return WEEK1_MONDAY + timedelta(weeks=slot - 1)

DAY_OFFSET = {"Monday": 0, "Tuesday": 1, "Wednesday": 2, "Thursday": 3,
              "Friday": 4, "Saturday": 5, "Sunday": 6}

def session_occurrences(s):
    day = s["day"]
    start_week = int(s.get("start_week", 1))
    end_week = int(s.get("end_week", NUM_WEEKS))
    for w in range(start_week, end_week + 1):
        yield w, teaching_week_monday(w) + timedelta(days=DAY_OFFSET[day])

# --- Build calendar ---
cal = Calendar()
cal.add("prodid", f"-//WorkBuddy Uni Course Scheduler//{meta['university']} {meta.get('semester_info','')}//CN")
cal.add("version", "2.0")
cal.add("calscale", "GREGORIAN")
cal.add("method", "PUBLISH")
cal.add("x-wr-calname", vText(f"{meta['university']} {meta['major']} {meta.get('semester_info','').split(',')[0].strip()}"))

# VTIMEZONE: auto-generate from TZID using icalendar's zoneinfo integration.
# Works for any IANA timezone (Northern/Southern hemisphere, with or without DST).
tz = Timezone.from_tzid(TIMEZONE_ID)
cal.add_component(tz)

# --- Add events ---
course_names = {c["course_code"]: c["course_name"] for c in data["course_overview"]["courses"]}
count = 0
for s in schedule:
    cc = s["course_code"]
    stype = s["session_type"]
    day = s["day"]
    start_hh, start_mm = s["start_time"].split(":")
    end_hh, end_mm = s["end_time"].split(":")
    campus = s.get("campus", "")
    building = s.get("building", "")
    room = s.get("room", "")
    notes = s.get("notes", "")
    location = " / ".join(x for x in [campus, building, room] if x and x != "TBA" and "TBA" not in x)
    if not location:
        location = campus

    for week, occ_date in session_occurrences(s):
        dtstart = datetime(occ_date.year, occ_date.month, occ_date.day, int(start_hh), int(start_mm))
        dtend = datetime(occ_date.year, occ_date.month, occ_date.day, int(end_hh), int(end_mm))
        if dtend <= dtstart:
            dtend = dtend + timedelta(days=1)

        e = Event()
        e.add("uid", f"{s['session_id']}-{occ_date.isoformat()}@workbuddy-coursescheduler")
        e.add("dtstamp", datetime.now(timezone.utc))
        e.add("dtstart", dtstart, parameters={"TZID": TIMEZONE_ID})
        e.add("dtend", dtend, parameters={"TZID": TIMEZONE_ID})
        e.add("summary", vText(f"{cc} {course_names.get(cc, '')} - {stype}"))
        desc = f"{cc} {course_names.get(cc, '')}\nSession: {stype}\nWeek: {week}/{NUM_WEEKS} (teaching week)"
        if notes:
            desc += f"\nNote: {notes}"
        e.add("description", vText(desc))
        e.add("location", vText(location))
        e.add("transp", "OPAQUE")
        e.add("status", "CONFIRMED")
        e.add("class", "PUBLIC")

        alarm = Alarm()
        alarm.add("action", "DISPLAY")
        alarm.add("description", vText(f"Reminder: {cc} {stype} in 15 minutes"))
        alarm.add("trigger", vDuration(timedelta(minutes=-15)))
        e.add_component(alarm)

        cal.add_component(e)
        count += 1

with open(OUTPUT, "wb") as f:
    f.write(cal.to_ical())

print(f"ICS generated: {OUTPUT} ({count} events across {len(schedule)} sessions, {NUM_WEEKS} teaching weeks minus excluded)")
