# 🚀 LeadGenius to HubSpot High-Speed Synchronization Pipeline

A robust, fully-automated Python integration pipeline designed to extract highly enriched leads from the [LeadGenius Automation API](https://www.leadgenius.com/) and dynamically inject them into [HubSpot CRM](https://www.hubspot.com/).

This repository serves as a fully functional CLI toolkit for RevOps engineers and SDR Managers looking to bypass manual CSV uploads and securely transfer rich, JSON-nested AI data attributes (scores, logic recommendations, complex company overviews, and HTML-formatted outreach emails) directly into custom CRM properties.

---

## ⚡ Core Features

*   **Global Rate-Limit Bypassing:** Utilizes native LeadGenius Administrative Tokens (`X-Admin-Key`) to securely and exponentially pull thousands of leads without facing the standard `HTTP 429 Too Many Requests` API bottlenecks.
*   **Dynamic CRM Schema Creation:** Intelligently pings the HubSpot `v3/properties` schema endpoints on execution. It dynamically establishes a dedicated "LeadGenius AI Insights" nested property group and creates 40+ custom properties natively under the `lg_` prefix exactly where they do not already exist.
*   **Idempotent Data Upserts:** Completely immune to duplication bugs. The pipeline batches lead profiles into 100-contact arrays and utilizes the HubSpot High-Volume Import API natively leveraging standard `Email` fields as programmatic uniqueness triggers.
*   **Deep JSON Payload Extraction:** Natively unpacks the highly-complex AI strings and `capture_all` arrays. Translates deeply nested `{"subject": "...", "content": "<br>"}` objects into pristine readable HubSpot text areas without HTML artifacts.
*   **Integer Force Formatting:** Automatically intercepts and cleans faulty string arrays (e.g., converting `"72.0"` natively to integer `'72'`) so that HubSpot filtering schemas operate reliably.

---

## 🛠 Prerequisites & Installation

### 1. Environment Setup

Ensure you have Python 3 installed. Navigate to the project root and install the basic required HTTP dependencies:

```bash
pip install requests python-dotenv
```

### 2. Required Authentication Variables (.env)

Create a strict `.env` file at the root of the project structure. Do not commit this file to version control.

```env
# Standard LeadGenius Token
LGP_API_KEY=your_standard_lg_token

# Administrative Token used explicitly for Global Limit Bypass
LGP_MASTER_KEY=your_x_admin_key_for_unlimited_speed

# HubSpot Private App Authentication Link
HUBSPOT_API_KEY=your_private_app_bearer_token
```

#### How to obtain your HubSpot Token
1. In HubSpot, navigate to **Settings > Integrations > Private Apps**.
2. Click **Create Private App** and name it `LeadGenius Sync`.
3. Under **Scopes**, absolutely ensure you grant:
   - `crm.objects.contacts.read` & `write`
   - `crm.schemas.contacts.read` & `write`
4. Copy your generated **Access Token**.

---

## 🚀 Usage Guide

### Full Database Synchronization
To completely orchestrate a global synchronization of your entire campaign array straight into your existing CRM layout:

```bash
python3 scripts/lg_full_to_hs.py
```

**Step-by-step Execution Flow:**
1. **Schema Check:** Quickly queries your portal schemas, automatically injecting custom properties (`lg_company_description`, `lg_ai_score`, etc.) safely into a dedicated folder without destructive overrides.
2. **Metadata Fetching:** Resolves thousands of Target Entity IDs sequentially.
3. **Payload Download:** Utilizing your `.env` master keys, caches fully-enriched JSON details for every Target Entity securely into local OS memory matrices.
4. **Mass Upload:** Formats arrays and blasts the cleaned, parsed leads directly to the CRM Batch injection endpoints seamlessly!

---

## 👔 Optimizing SDR Workflows inside HubSpot

Due to HubSpot API limitations prohibiting external scripts from rewriting UI View interfaces, SDR Administrators must manually execute the following layout tweaks to extract maximum value from this synchronization:

1. **The SDR View (Table Layout):** Navigate to **Contacts > Add View > Create New View**. Surface target columns: `Mobile Phone`, `LG AI Score`, `LG Recommendation`, `LG LinkedIn URL`. Save this View as a Shared Entity so the entire outbound floor can execute down the pipeline flawlessly.
2. **The Sales Dashboard Sidebar (Record Level):** Click the Settings gear, go to **Objects > Contacts > Record Customization**, and edit the **Left Sidebar**. Create a structural component titled **LeadGenius AI Insights** and pin all `lg_` properties directly to the top so Sales Development Reps don't have to scroll to view AI analytics during live calls.

---

*This project structure integrates universally with modern Anthropic AI Coding standard practices (SKILL.md). Check the bundled SKILL.md file for the specialized execution patterns used by internal autonomous IDE agents.*
