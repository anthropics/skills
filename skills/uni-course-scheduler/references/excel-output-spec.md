# Excel Output Specification — 6-Sheet Workbook

The generated Excel workbook follows the ai-university-course-planner-schema
with 6 sheets. Each sheet serves a specific purpose in the course planning
workflow.

---

## Sheet 1: Course Overview

Master catalog of all available courses extracted from the university catalog.

**Key columns:** Course Code, Course Name, Description, Credits, Credit System,
Course Type, Department, Faculty, Level, Prerequisites, Corequisites,
Antirequisites, Duration (Weeks), Contact Hours/Week, Assessment Types,
Enrolment Cap, Enrolment Difficulty, Student Rating, Handbook URL,
Available Semesters, i18n Key, Last Updated, Is Active

**Formatting:**
- Required courses: dark red background, white bold text
- Major Elective: green background, white text
- Very Hard enrolment: medium red border
- Hard enrolment: medium orange border

---

## Sheet 2: Degree Planner

Two sections:
- **Section A:** Degree requirements tracker (category, min credits, completed,
  remaining, status)
- **Section B:** Semester enrolment plan (course code, requirement ID, semester,
  status, priority, credits, grade, grade points)

**Formatting:**
- Completed status: green fill, white text
- Planned status: blue fill, white text
- Failed status: red fill, white bold text

---

## Sheet 3: AI Recommendations

AI-generated course suggestions with reasoning and alternatives.

**Key columns:** Recommendation ID, Course Code, Reason, Recommendation Type,
Confidence Score, Priority, Recommended Semester, Alternatives, Decision,
Decision Timestamp, Resulting Plan ID, Generated At, Expires At

**Formatting:**
- Confidence >= 0.9: gold background
- Confidence < 0.5: light red background
- Critical priority: dark red fill, white bold text

---

## Sheet 4: Weekly Timetable

Visual grid: rows = time slots (08:00-22:00, 30-min increments),
columns = Monday-Sunday.

**Cell content:** Course Code, Session Type, Location, Instructor

**Color rules by course type:**
- Required: dark red fill, white bold text
- Major Elective: green fill, white text
- General Education: blue fill, white text

**Color rules by session type:**
- Lab: purple fill, white text
- Tutorial: light blue fill
- Workshop: orange fill, white text

**Empty cells:** grey fill (free time)

---

## Sheet 5: Academic Calendar

Institution-wide academic dates.

**Key columns:** Event ID, Event Name, Event Type, Start Date, End Date,
Start Time, End Time, Semester Code, Is Recurring, Recurrence Rule, Location,
Description, Calendar UID, Reminder (Minutes)

**Formatting:**
- Holiday: yellow fill
- Exam Period: red fill, white text
- Break: light blue fill

---

## Sheet 6: Raw Schedule Database

Normalized session data (hidden by default).

**Key columns:** Session ID, Course Code, Session Type, Day, Start Time,
End Time, Campus, Building, Room, Instructor, Week Pattern, Start Week,
End Week, Effective From, Effective Until, Notes

This sheet is the machine-readable source of truth. The Weekly Timetable sheet
is a visual projection of this data.
