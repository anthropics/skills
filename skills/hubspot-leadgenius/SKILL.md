---
name: hubspot-leadgenius
description: Use this skill whenever the user asks to import, sync, migrate, or export leads from LeadGenius into HubSpot. This is the definitive guide and toolset for LeadGenius to HubSpot integration. Covers Private App setup, schema creation, rate-limit bypassing (using X-Admin-Key), JSON parsing for AI scores/emails/company descriptions, and batch upserts using the HubSpot v3 APIs.
---

# LeadGenius → HubSpot Import API Pipeline

> How to fully automate the extraction of enriched leads from LeadGenius and synchronize them natively into a HubSpot portal, with dynamic property group creation and exhaustive AI insight payload parsing.

---

## Table of Contents

0. [Overview](#0-overview)
1. [Prerequisites](#1-prerequisites)
2. [Creating the HubSpot Private App](#2-creating-the-hubspot-private-app)
3. [LeadGenius API Configuration & Bypass](#3-leadgenius-api-configuration--bypass)
4. [LeadGenius JSON Field Reference](#4-leadgenius-json-field-reference)
5. [Creating Custom Properties inside HubSpot](#5-creating-custom-properties-inside-hubspot)
6. [Importing Contacts & Data Mapping](#6-importing-contacts--data-mapping)
7. [Creating Saved Views (For SDRs)](#7-creating-saved-views-for-sdrs)
8. [Complete Automated Execution](#8-complete-automated-execution)
9. [Troubleshooting](#9-troubleshooting)

---

## 0. Overview

### What This Does

```text
LeadGenius Automation API  →  HubSpot Contacts Database
 Over 120 nested objects       Native Custom CRM Properties
  Full X-Admin-Key Bypass      Property Group (LeadGenius AI)
```

### Architecture

The LeadGenius API structure is highly complex, often burying core intel like Company Descriptions and direct phone arrays inside concatenated pipe-separated `:Mobile: | :Direct:` strings or JSON-wrapped string layers (`{"subject": "...", "content": "..."}`).

This guide bridges the gap structurally by:
1. **Dynamic Authentication:** Using `X-Admin-Key` arrays to completely override LeadGenius standard API throttling bottlenecks.
2. **Schema Standardization:** Emitting native HTTP POST requests to create a localized `leadgenius_data` Property Group on HubSpot immediately upon bootstrap.
3. **Deep Extraction:** Natively unpacking AI analysis, recommendation texts, and formatting integer matrices without UI friction.
4. **Massive Deduplication:** Launching 100-batch recursive endpoints routing via HubSpot's High-Level Upsert endpoints triggering on standard `email` objects.

### API Strategy Summary

| Operation | API Used | Why |
|-----------|----------|-----|
| HubSpot Authentication | Private App Token (Bearer) | Immediate API routing with no OAuth authorization hassle. |
| LeadGenius Fast Extraction | `X-Admin-Key` Headers | Overrides the typical API rate limits (HTTP 429) natively. |
| Create Property Group | `crm/v3/properties/groups` | Ensures all AI parameters don't clutter the global CRM view. |
| Create Properties | `crm/v3/properties/contacts`| Establishes schema integrity instantly without manual input. |
| Insert/Update Leads | `crm/v3/objects/contacts/batch/upsert`| Standard CRUD handling utilizing `idProperty: email`. |
| Create List Views | ❌ Manual Process | HubSpot restricts visual dashboard component programmatic builds. |

---

## 1. Prerequisites

### Software Requirements

```bash
pip3 install requests python-dotenv
```

### Environment Configuration

Create a local `.env` file at the root of your execution directory securely:

```env
# LeadGenius
LGP_API_KEY=your_standard_lg_token
LGP_MASTER_KEY=your_admin_bypass_token

# HubSpot
HUBSPOT_API_KEY=your_private_app_bearer_token
```

---

## 2. Creating the HubSpot Private App

In order to seamlessly authorize interactions with your Hubspot infrastructure, you must secure a native Private App token.

1. Click the **⚙️ Settings** icon in your HubSpot main navigation bar.
2. In the left sidebar, route to **Integrations > Private Apps**.
3. Click **Create private app**.
4. Basic Info: Name your deployment `LeadGenius Sync`.
5. Under the **Scopes** tab, explicitly inject these functional read/write headers:
   - `crm.objects.contacts.read`
   - `crm.objects.contacts.write`
   - `crm.schemas.contacts.read`
   - `crm.schemas.contacts.write`
6. Click **Create app** and securely port your new Access Token directly to `HUBSPOT_API_KEY` in your `.env`.

---

## 3. LeadGenius API Configuration & Bypass

Standard integrations fail aggressively on large environments because LeadGenius throttles basic API tokens recursively. We invoke native administrative clearance bypassing this framework utilizing `X-Admin-Key`.

When querying the core lead engine, we establish dual headers natively:
```python
LG_HEADERS = {
    'X-API-Key': os.getenv('LGP_API_KEY'),
    'X-Admin-Key': os.getenv('LGP_MASTER_KEY')
}
import requests
r = requests.get("https://api.leadgenius.app/api/automation/leads", headers=LG_HEADERS)
```

> [!CAUTION]
> When `X-Admin-Key` is utilized natively, the LeadGenius API structurally shifts the standard JSON payload directly inside an isolated `data` dictionary layer. Any scripts targeting `.get('id')` will fatally fail unless structurally targeting `.get('data', {}).get('id')`.

---

## 4. LeadGenius JSON Field Reference

LeadGenius exports deep multi-layered JSON metadata. We meticulously map these dynamically into HubSpot.

### Standard Field Mapping (Base Infrastructure)

| LeadGenius Object Column | HubSpot Internal ID | Execution Action |
|-------------------------|---------------------|------------------|
| `firstName` | `firstname` | |
| `lastName` | `lastname` | Maps to "Unknown" if natively null. |
| `title` | `jobtitle` | |
| `companyName` | `company` | |
| `email` | `email` | Serves as the primary ID key for Batch Upsert arrays. |

### Complex AI Extraction Fields (Custom Framework)

| LeadGenius Nested Object | HubSpot Internal Structure | Python Filter Strategy |
|--------------------------|----------------------------|------------------------|
| `aiLeadScore.ai_score` | `lg_ai_score` | Parsed securely via `int(float(val))` removing decimal vectors natively. |
| `capture_all > :Company Description:` | `lg_company_description` | Regex mapped natively overriding limited `companyValueProp` matrices. |
| `phoneNumber` / `sanitizedPhoneNumber` | `mobilephone` | Resolves uniquely against HQ endpoints strictly using standard direct routes. |
| `ai1` / `aiColdEmail` | `lg_cold_email` | Structurally stringified clearing heavily fragmented `{"subject"}` objects and `<br>` elements natively. |
| `aiScoreJustification` | `lg_justification` | Safely encoded utilizing multi-line parameters stripping `\n` carriage limits. |
| `aiScoreRecommendation` | `lg_recommendation` | Text-area extraction. |

### Enrichment Target References

| Target Endpoint | HubSpot Structural Map | Type Format |
|-----------------|------------------------|-------------|
| `linkedinUrl` | `lg_linkedin_url` | URL Block |
| `companyLinkedinUrl` | `lg_company_linkedin` | URL Block |
| `seniority` | `lg_seniority` | Text Format |

---

## 5. Creating Custom Properties inside HubSpot

All integrated properties must systematically map to `lg_` prefixed tables under a master `leadgenius_data` component.

### Example Schema Execution Array

The following snippet natively configures standard extraction components automatically:

```python
import requests, os
from dotenv import load_dotenv

load_dotenv()
HS_HEADERS = {
    'Authorization': f"Bearer {os.getenv('HUBSPOT_API_KEY')}",
    'Content-Type': 'application/json'
}

def setup_properties():
    # 1. Establish Property Group
    group_req = requests.post(
        'https://api.hubapi.com/crm/v3/properties/contacts/groups',
        headers=HS_HEADERS,
        json={"name": "leadgenius_data", "displayOrder": -1, "label": "LeadGenius AI Data"}
    )
    
    # 2. Extract and Post Objects
    properties = [
        {"name": "lg_ai_score", "label": "LG AI Score", "type": "number", "fieldType": "number", "groupName": "leadgenius_data"},
        {"name": "lg_company_description", "label": "LG Company Description", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
        # Added extra...
    ]
    
    for prop in properties:
        requests.post('https://api.hubapi.com/crm/v3/properties/contacts', headers=HS_HEADERS, json=prop)
```

---

## 6. Importing Contacts & Data Mapping

Once schema arrays are structurally localized on HubSpot, you bypass the standard REST API limits using High-Volume Endpoints (`batch/upsert`).

```python
def build_hs_contact(lead):
    # Parses unique JSON strings
    def parse_email_json(text):
        if not text: return ""
        try:
            import json
            parsed = json.loads(text)
            return f"Subject: {parsed.get('subject', '')}\n\n{parsed.get('content', '')}".replace('<br>', '\n')
        except: return str(text).replace('<br>', '\n')

    props = {
        "email": lead.get('email'),
        "firstname": lead.get('firstName'),
        "lg_ai_score": str(int(float(lead.get('aiLeadScore', {}).get('ai_score', 0)))),
        "lg_company_description": lead.get('capture_all_parsed', {}).get('Company Description')
    }
    return {k: v for k, v in props.items() if v}

# Batch Upsert Loop
chunk = leads[0:100]
inputs = [{"idProperty": "email", "id": c['email'], "properties": c} for c in chunk if c.get('email')]

response = requests.post(
    'https://api.hubapi.com/crm/v3/objects/contacts/batch/upsert', 
    headers=HS_HEADERS, 
    json={"inputs": inputs}
)
```

---

## 7. Creating Saved Views (For SDRs)

UI Saved Layouts cannot be programmatically initiated via Standard Endpoints securely. Administrators must instruct internal teams utilizing the following manual pipeline layout configurations:

1. Launch HubSpot and access the **Contacts Data Table**.
2. Navigate directly to **Add View > Create New View** and define `SDR LeadGenius Outbound`.
3. Select **Edit Columns** and firmly integrate:
   - `Lead Status`
   - `LG AI Score`
   - `LG Recommendation`
   - `Mobile Phone`
4. Make sure your SDR operators utilize **Settings > Objects > Contacts > Record Customization** natively to permanently anchor the `leadgenius_data` sidebar at the apex of user visual fields on the Contact Card.

---

## 8. Complete Automated Execution

The unified deployment matrix script integrating Schema Build, Extraction Arrays, Bypass Authentication, JSON Sanitization string manipulation, and Batch Array POSTing natively is available securely within the executed script pipeline.

Simply run recursively:
```bash
python3 scripts/lg_full_to_hs.py
```

---

## 9. Troubleshooting

| Error Code/Symptom | Direct Internal Cause | Execution Fix |
|--------------------|-----------------------|---------------|
| `PROPERTY_DOESNT_EXIST` | Script failed to setup custom Schema. | Wipe memory cache and rerun step 1 property validation. |
| `KeyError: 'data'` | The LeadGenius script failed to use `X-Admin-Key` properly. | Verify the `LGP_MASTER_KEY` is fully established in standard `.env`. |
| Zero Properties Imported | The Batch API failed matching standard fields. | Ensure array targets the CRM Endpoint Native Field Identifier mapping (`email`). |
| `HTTP 429` | Reverted to Standard LeadGenius Limits. | Confirm bypass admin keys are pushed exactly as `X-Admin-Key`. |
