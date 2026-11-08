# Cloud Output Format — Expected JSON Structure

When the LoomLoom SkillBot finishes a run, each row of the workbook returns
JSON outputs. The combined output is passed to `scripts/generate_excel.py`.

## Combined Input JSON

```json
{
  "meta": {
    "university": "University of Melbourne",
    "major": "Computer Science",
    "year_level": "Year 1",
    "education_system": "Australian Credit Points",
    "semester_info": "2026-S1, starts 2026-02-24, ends 2026-06-05, 12 teaching weeks"
  },
  "course_overview": {
    "university": "University of Melbourne",
    "major": "Computer Science",
    "credit_system": "Australian Credit Points",
    "courses": [
      {
        "course_code": "COMP10001",
        "course_name": "Foundations of Computing",
        "description": "Introduction to computer science fundamentals.",
        "credits": 12.5,
        "credit_system": "Australian Credit Points",
        "course_type": "Required",
        "department": "Computer Science",
        "faculty": "Engineering and IT",
        "level": "Introductory",
        "prerequisites": "",
        "corequisites": "",
        "antirequisites": "",
        "duration_weeks": 12,
        "contact_hours_per_week": 4,
        "assessment_types": "Exam, Assignment, Project",
        "enrolment_difficulty": "Moderate",
        "enrolment_cap": 300,
        "student_rating": 4.2,
        "handbook_url": "https://handbook.unimelb.edu.au/...",
        "available_semesters": "S1,S2",
        "is_active": true
      }
    ]
  },
  "recommendations": {
    "mode": "ai_recommend",
    "total_recommended_credits": 50,
    "recommendations": [
      {
        "course_code": "COMP10001",
        "reason": "Core requirement for Computer Science major.",
        "recommendation_type": "Requirement Fulfilment",
        "confidence_score": 0.95,
        "priority": "Critical",
        "alternatives": ["COMP10002"],
        "prerequisite_warning": "",
        "difficulty": 3,
        "workload": "Medium",
        "assessment": "Exam, Assignment",
        "recommended_semester": "2026-S1"
      }
    ]
  },
  "weekly_schedule": {
    "schedule": [
      {
        "session_id": "SESS-COMP10001-LEC-01",
        "course_code": "COMP10001",
        "session_type": "Lecture",
        "day": "Monday",
        "start_time": "09:00",
        "end_time": "10:00",
        "campus": "Parkville",
        "building": "Doug McDonell",
        "room": "G03",
        "instructor": "Dr. Smith",
        "week_pattern": "Every Week",
        "start_week": 1,
        "end_week": 12,
        "effective_from": "2026-02-24",
        "effective_until": "2026-06-05"
      }
    ],
    "conflict_detection": [],
    "daily_density": [
      {
        "day": "Monday",
        "total_hours": 4,
        "session_count": 3,
        "intensity_rating": "Medium"
      }
    ],
    "lunch_break_preserved": {
      "Monday": true,
      "Tuesday": true
    },
    "enrollment_priority_list": [
      {
        "course_code": "COMP10001",
        "priority": "Critical"
      }
    ]
  }
}
```

## Output Sections

### Catalog Analysis Output
Returns the `course_overview` object with an array of course objects.

### Recommendation Output
Returns the `recommendations` object with recommendation entries.

### Schedule Output
Returns the `weekly_schedule` object with session entries, conflict detection,
daily density, and enrollment priority list.

## Missing Data Handling

Any field not found in the catalog should be set to the string `"NOT_FOUND"`.
The `generate_excel.py` script converts this to `"— (not found, please add)"`
in the Excel output.
