import csv, requests, os, sys
from dotenv import load_dotenv

load_dotenv()
TOKEN = os.getenv('HUBSPOT_ACCESS_TOKEN')
if not TOKEN:
    print("❌ ERROR: HUBSPOT_ACCESS_TOKEN not mapped in .env")
    sys.exit(1)

HEADERS = {
    'Authorization': f"Bearer {TOKEN}",
    'Content-Type': 'application/json'
}

PROPERTIES = [
    {"name": "lg_ai_score", "label": "LG AI Score", "type": "number", "fieldType": "number", "groupName": "leadgenius_data"},
    {"name": "lg_qualification", "label": "LG Qualification", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_justification", "label": "LG Justification", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_next_action", "label": "LG Next Action", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_cold_email", "label": "LG Cold Email", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_likely_engage", "label": "LG Likely to Engage", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_linkedin_url", "label": "LG LinkedIn URL", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_seniority", "label": "LG Seniority", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_lead_id", "label": "LG Lead ID", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"}
]

def safe_str(val): return str(val).strip() if val else ""

def setup_properties():
    print("--- 1. Setting up HubSpot Properties ---")
    group_payload = {"name": "leadgenius_data", "displayOrder": -1, "label": "LeadGenius AI Data"}
    requests.post('https://api.hubapi.com/crm/v3/properties/contacts/groups', headers=HEADERS, json=group_payload)
    
    for prop in PROPERTIES:
        r = requests.post('https://api.hubapi.com/crm/v3/properties/contacts', headers=HEADERS, json=prop)
        if r.status_code == 201: print(f"  ✅ Created: {prop['name']}")
        elif "already exists" in r.text: print(f"  ⏭️ Skipped: {prop['name']}")

def upsert_contacts(csv_file):
    print(f"\n--- 2. Upserting Contacts from {csv_file} ---")
    if not os.path.exists(csv_file):
        print(f"❌ ERROR: File {csv_file} not found.")
        return

    with open(csv_file, 'r', encoding='utf-8-sig') as f:
        rows = list(csv.DictReader(f))

    batch_size = 100
    for i in range(0, len(rows), batch_size):
        chunk = rows[i:i+batch_size]
        inputs = []
        for row in chunk:
            if not row.get('Email'): continue
            inputs.append({
                "idProperty": "email",
                "id": safe_str(row.get('Email')),
                "properties": {
                    "firstname": safe_str(row.get('First Name')),
                    "lastname": safe_str(row.get('Last Name')) or "Unknown",
                    "jobtitle": safe_str(row.get('Title')),
                    "company": safe_str(row.get('Company Name')),
                    "lg_ai_score": safe_str(row.get('Ai Score Value')),
                    "lg_qualification": safe_str(row.get('Ai Qualification')),
                    "lg_justification": safe_str(row.get('Ai Score Justification')),
                    "lg_cold_email": safe_str(row.get('Ai Cold Email')),
                    "lg_linkedin_url": safe_str(row.get('Linkedin Url'))
                }
            })
        if inputs:
            r = requests.post('https://api.hubapi.com/crm/v3/objects/contacts/batch/upsert', headers=HEADERS, json={"inputs": inputs})
            if r.status_code in [200, 201, 204]:
                print(f"  ✅ Batch {i} to {i+len(chunk)} upserted successfully.")
            else:
                print(f"  ❌ Batch error: {r.text[:200]}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 lg_to_hs.py <file.csv>")
        sys.exit(1)
    setup_properties()
    upsert_contacts(sys.argv[1])
