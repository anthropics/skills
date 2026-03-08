# Notifications

## Notification Types

```
Email Notifications (sysevent_email_action)
  - Record-based: triggered by insert/update/delete on a table
  - Event-based: triggered by system events (sysevent)
  - Scheduled: sent on a schedule

Push Notifications (sys_push_notification)
  - Mobile app push notifications
  - Now Mobile, Agent Mobile

SMS Notifications (sys_sms_notification) 
  - Via SMS gateway integration
  - Twilio, AT&T, custom providers
```

## Email Notifications

### Creating a Notification
```
Navigate: System Notification > Email > Notifications
Table: sysevent_email_action

Key fields:
  - Name: descriptive name
  - Table: target table (e.g., incident)
  - When to send:
    - Record inserted
    - Record updated
    - Record inserted or updated
    - Event is fired
  - Conditions: filter for when notification applies
  - Who will receive:
    - Users in fields (assigned_to, opened_by, etc.)
    - Groups
    - Users/Groups in related tables
    - Event parm 1 / parm 2 recipients
    - Explicit email addresses
  - Weight: priority (higher weight = higher priority when throttled)
```

### Condition-Based Notification
```
Name: P1 Incident Assigned
Table: incident
When: Record updated
Conditions:
  - Priority = 1 - Critical
  - Assigned to changes
  - Active = true
  
Send to:
  - Users in fields: Assigned to
  - Also CC: Assignment group manager
  
Subject: [${number}] Critical Incident Assigned to You: ${short_description}
```

### Event-Based Notification
```
Name: Password Reset Confirmation  
Table: sys_user
When: Event is fired
Event name: user.password.reset

Send to:
  - Event parm 1 (contains user sys_id)
  
Subject: Password Reset Successful
Body: Your password has been reset. If you did not request this, contact IT immediately.
```

### Firing Custom Events
```javascript
// Server script — fire a custom event
// Parameters: event_name, record, parm1, parm2
gs.eventQueue('custom.incident.escalated', current, 
    current.assigned_to.toString(),  // parm1: recipient user sys_id
    current.getValue('number')        // parm2: additional context
);
```

## Email Templates

### Mail Script (Advanced)
```
Table: sys_script_email
Use: Dynamic content in notification body

Example: Include related change requests
```
```javascript
// Mail Script: include_related_changes
(function runMailScript(current, template, email, email_action, event) {
    var changes = [];
    var gr = new GlideRecord('change_request');
    gr.addQuery('cmdb_ci', current.getValue('cmdb_ci'));
    gr.addQuery('state', 'IN', '-5,-4,-3,-2,-1');  // Open states
    gr.orderByDesc('sys_created_on');
    gr.setLimit(5);
    gr.query();
    
    while (gr.next()) {
        changes.push(gr.getValue('number') + ' - ' + gr.getValue('short_description'));
    }
    
    if (changes.length > 0) {
        template.print('<h3>Related Open Changes:</h3><ul>');
        for (var i = 0; i < changes.length; i++) {
            template.print('<li>' + changes[i] + '</li>');
        }
        template.print('</ul>');
    } else {
        template.print('<p>No related open changes found.</p>');
    }
})(current, template, email, email_action, event);
```

### Using Mail Scripts in Notifications
```html
<!-- In notification body (HTML) -->
<h2>Incident ${number} - ${short_description}</h2>
<p>Priority: ${priority}</p>
<p>State: ${state}</p>

<!-- Insert mail script output -->
${mail_script:include_related_changes}

<!-- Standard fields -->
<p>Assigned to: ${assigned_to.name}</p>
<p>Assignment group: ${assignment_group.name}</p>

<!-- Link to record -->
<p><a href="${URI_REF}">View Incident</a></p>
```

### Email Layout
```
Table: sysevent_email_template
Use: Consistent branding across all notifications

Structure:
  - Header (logo, company name)
  - Body (notification-specific content inserted here)
  - Footer (unsubscribe link, legal text)

Key field: Message HTML with ${body} placeholder
```

## Notification Preferences

### User Preferences
```
Navigate: System Notification > Email > Notification Preferences

Users can:
  - Opt out of specific notifications
  - Change delivery channel (email, SMS, push)
  - Set digest schedules (hourly, daily summary)
  
Admin controls:
  - Mandatory notifications (users cannot opt out)
  - Device-specific settings
```

### Digest Notifications
```
Navigate: System Notification > Email > Notifications > Digest tab

Configuration:
  - Interval: Hourly, Daily, Weekly
  - Send time: specific time of day
  - Group by: table, category, or custom
  
Use case: Instead of 50 individual emails, 
  send one daily digest of all P3-P4 incident updates
```

## Inbound Email Actions

### Processing Incoming Emails
```
Table: sysevent_in_email_action
Use: Create/update records from incoming emails

Example: Create incident from email
  Target table: incident
  Conditions: 
    - Subject contains "URGENT" or "incident"
    - From address is in sys_user
    
Action script:
```
```javascript
// Inbound email action script
(function runAction(current, event, email, logger) {
    // current = target record (incident)
    // email = incoming email object
    
    current.setValue('short_description', email.subject);
    current.setValue('description', email.body_text);
    current.setValue('caller_id', email.from);  // Auto-matches to sys_user
    current.setValue('contact_type', 'email');
    
    // Parse priority from subject
    if (email.subject.indexOf('[P1]') > -1) {
        current.setValue('priority', '1');
    } else if (email.subject.indexOf('[P2]') > -1) {
        current.setValue('priority', '2');
    }
    
    // Handle attachments
    // Attachments are auto-attached to the record
    
    current.insert();
    
    // Reply to sender
    email.setReplyTo(current);  // Future replies thread to this record
    
})(current, event, email, logger);
```

### Reply Processing (Threading)
```javascript
// Inbound action for replies (updates existing record)
(function runAction(current, event, email, logger) {
    // current = existing incident (matched by watermark in email)
    
    // Add email body as work note
    current.setValue('work_notes', 'Email from ' + email.from + ':\n' + email.body_text);
    current.update();
    
})(current, event, email, logger);
```

## SMS Notifications

### Configuration
```
Navigate: System Notification > SMS > SMS Configuration

Setup:
  1. Configure SMS provider (Twilio, etc.)
  2. Set up SMS Notification records
  3. Map phone numbers to user records

Twilio Integration:
  - Account SID, Auth Token
  - From Number
  - REST endpoint: api.twilio.com
```

### SMS Notification Record
```
Table: sys_sms_notification
Similar to email notifications but:
  - Character limit (160 for SMS, varies for MMS)
  - No HTML formatting
  - Phone number field required on user record
  
Message template:
  "${number} ${priority} incident assigned to you: ${short_description}. Reply ACKNOWLEDGE to accept."
```

## Push Notifications

### Mobile Push Configuration
```
Navigate: System Notification > Push > Push Notifications

Setup:
  - Firebase Cloud Messaging (FCM) for Android
  - Apple Push Notification Service (APNs) for iOS
  - ServiceNow Mobile App handles registration
  
Push Notification record:
  - Table, Conditions (same as email)
  - Title, Body (shorter than email)
  - Deep link: opens specific record in mobile app
```

## Notification Troubleshooting

### Debug Notifications
```
Navigate: System Notification > Email > Notifications

Diagnostics:
  1. System Logs > Email Log — see all sent/failed emails
  2. System Diagnostics > Email — check SMTP connectivity
  3. Notification Preview — test with a specific record
  
Common issues:
  - SMTP not configured (System Mailboxes > Outbound)
  - Email address missing on user record
  - Notification inactive
  - Conditions not met (test with a known record)
  - Spam filter blocking ServiceNow domain
  - Email throttled (check weight/throttle settings)
```

### Testing Notifications
```javascript
// Fix Script — manually trigger a notification for testing
var rec = new GlideRecord('incident');
if (rec.get('number', 'INC0012345')) {
    // Fire event that notification listens to
    gs.eventQueue('incident.assigned', rec,
        rec.getValue('assigned_to'),
        rec.getValue('number'));
}

// OR trigger notification directly
var notify = new SNCEmailSender();
notify.send(rec, 'your_notification_sys_id');
```

## Best Practices

1. **Event-based > direct** — decouple notification from transaction processing
2. **Digest for low-priority** — reduce email fatigue
3. **Mandatory for critical** — P1 incident notifications should not be opt-outable
4. **Mail scripts for dynamic content** — don't cram logic into notification body
5. **Test with Notification Preview** — before activating in production
6. **Monitor email logs** — failed deliveries often go unnoticed
7. **Unsubscribe links** — include in footer for GDPR/CAN-SPAM compliance
8. **Don't over-notify** — every unnecessary email erodes trust in the system
9. **Use weight field** — prioritize critical notifications during throttle periods
10. **Template your layouts** — consistent branding builds user confidence
