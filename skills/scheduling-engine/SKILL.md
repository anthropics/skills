---
name: scheduling-engine
description: AI-powered appointment scheduling with staff management, availability windows, and booking automation.
author: MCF Agentic
version: 1.0.0
tags: [scheduling, appointments, booking, calendar, availability, staff-management]
pricing: x402 (USDC on Base)
gateway: https://gateway.mcfagentic.com
---

# Scheduling Engine

Manage appointments, staff schedules, and availability windows programmatically. Built for AI agents that need to book meetings, manage calendars, and coordinate schedules as part of sales, service, or operations workflows. Handles timezone conversion, conflict detection, and smart slot suggestions.

## Authentication

All endpoints require x402 payment (USDC on Base L2). Send a request without payment to receive pricing info in the 402 response.

## Endpoints

### Create Appointment
- **Method:** POST
- **Path:** /api/scheduling/appointments
- **Price:** $0.05 per call
- **Description:** Book an appointment. Automatically checks for conflicts and confirms availability.

**Request:**
```json
{
  "title": "Discovery Call - Comfort Zone HVAC",
  "start_time": "2026-04-03T10:00:00-05:00",
  "duration_minutes": 30,
  "staff_id": "staff_cameron",
  "attendees": [
    {"name": "Mike Torres", "email": "mike@comfortzonehvac.com"}
  ],
  "type": "discovery-call",
  "notes": "Interested in AI scheduling bundle, $497/mo",
  "send_confirmation": true
}
```

**Response:**
```json
{
  "id": "apt_6r2nw8",
  "title": "Discovery Call - Comfort Zone HVAC",
  "start_time": "2026-04-03T10:00:00-05:00",
  "end_time": "2026-04-03T10:30:00-05:00",
  "staff_id": "staff_cameron",
  "status": "confirmed",
  "confirmation_sent": true,
  "meeting_link": "https://meet.mcfagentic.com/apt_6r2nw8"
}
```

### List Appointments
- **Method:** GET
- **Path:** /api/scheduling/appointments
- **Price:** $0.02 per call
- **Description:** List appointments with optional filters for date range, staff, and status.

**Request:**
```
GET /api/scheduling/appointments?staff_id=staff_cameron&start_date=2026-04-01&end_date=2026-04-07
```

**Response:**
```json
{
  "appointments": [
    {
      "id": "apt_6r2nw8",
      "title": "Discovery Call - Comfort Zone HVAC",
      "start_time": "2026-04-03T10:00:00-05:00",
      "duration_minutes": 30,
      "status": "confirmed"
    }
  ],
  "total": 1
}
```

### Manage Staff
- **Method:** POST
- **Path:** /api/scheduling/staff
- **Price:** $0.03 per call
- **Description:** Create or update staff profiles. Define who can be booked and their default settings.

**Request:**
```json
{
  "name": "Cameron Fagan",
  "email": "cameron@mcfagentic.com",
  "timezone": "America/Chicago",
  "default_meeting_duration": 30,
  "booking_buffer_minutes": 15,
  "max_daily_meetings": 8
}
```

**Response:**
```json
{
  "id": "staff_cameron",
  "name": "Cameron Fagan",
  "timezone": "America/Chicago",
  "status": "active"
}
```

### Check Availability
- **Method:** GET
- **Path:** /api/scheduling/availability-windows
- **Price:** $0.02 per call
- **Description:** Get available time slots for a staff member within a date range. Returns bookable windows accounting for existing appointments and buffer times.

**Request:**
```
GET /api/scheduling/availability-windows?staff_id=staff_cameron&date=2026-04-03&duration=30
```

**Response:**
```json
{
  "staff_id": "staff_cameron",
  "date": "2026-04-03",
  "timezone": "America/Chicago",
  "available_slots": [
    {"start": "09:00", "end": "09:30"},
    {"start": "10:30", "end": "11:00"},
    {"start": "11:00", "end": "11:30"},
    {"start": "13:00", "end": "13:30"},
    {"start": "14:00", "end": "14:30"},
    {"start": "15:00", "end": "15:30"}
  ]
}
```

### Set Availability Windows
- **Method:** POST
- **Path:** /api/scheduling/availability-windows
- **Price:** $0.03 per call
- **Description:** Define recurring availability windows for a staff member. Set working hours, blocked times, and day-off overrides.

**Request:**
```json
{
  "staff_id": "staff_cameron",
  "recurring": [
    {"day": "monday", "start": "09:00", "end": "17:00"},
    {"day": "tuesday", "start": "09:00", "end": "17:00"},
    {"day": "wednesday", "start": "09:00", "end": "17:00"},
    {"day": "thursday", "start": "09:00", "end": "17:00"},
    {"day": "friday", "start": "09:00", "end": "12:00"}
  ],
  "blocked": [
    {"date": "2026-04-04", "reason": "Company holiday"}
  ]
}
```

**Response:**
```json
{
  "staff_id": "staff_cameron",
  "availability_updated": true,
  "next_available": "2026-04-03T09:00:00-05:00"
}
```

## Use Cases

- A sales agent books a discovery call after a lead expresses interest via email
- An AI receptionist checks availability and schedules appointments from inbound requests
- A service agent coordinates technician schedules for work order fulfillment
- An orchestrator agent manages a consultant's calendar across multiple client engagements
- A follow-up agent reschedules missed appointments automatically

## Pricing

| Endpoint | Price | Description |
|----------|-------|-------------|
| /api/scheduling/appointments (POST) | $0.05 | Create an appointment |
| /api/scheduling/appointments (GET) | $0.02 | List appointments |
| /api/scheduling/staff | $0.03 | Create/update staff profiles |
| /api/scheduling/availability-windows (GET) | $0.02 | Check available slots |
| /api/scheduling/availability-windows (POST) | $0.03 | Set availability rules |
