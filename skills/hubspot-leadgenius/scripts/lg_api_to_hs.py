import requests, os, sys, math
from dotenv import load_dotenv

load_dotenv()
HS_TOKEN = os.getenv('HUBSPOT_API_KEY')
LG_TOKEN = os.getenv('LGP_API_KEY')

if not HS_TOKEN or not LG_TOKEN:
    print("❌ ERROR: Missing HUBSPOT_API_KEY or LGP_API_KEY from .env")
    sys.exit(1)

HS_HEADERS = {'Authorization': f"Bearer {HS_TOKEN}", 'Content-Type': 'application/json'}
LG_HEADERS = {'X-API-Key': LG_TOKEN}
CLIENT_ID = "6eceb43b-5c1a-4c4d-898c-36e67b24fdc6" # SCC Software - IT Automation

PROPERTIES = [
    {"name": "lg_linkedin_url", "label": "LG LinkedIn URL", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_lead_id", "label": "LG Lead ID", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_ai_score", "label": "LG AI Score", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_cold_email", "label": "LG Cold Email", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai1", "label": "LG AI 1 (Raw)", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai2", "label": "LG AI 2 (Raw)", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai3", "label": "LG AI 3 (Raw)", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"}
]

def safe_str(val): return str(val).strip() if val and val != 'N/A' else ""

def fetch_all_lg_leads():
    print(f"\n--- Fetching Leads from LeadGenius (Client: {CLIENT_ID}) ---")
    leads = []
    url = f"https://api.leadgenius.app/api/automation/leads?client_id={CLIENT_ID}&limit=500"
    
    while url:
        r = requests.get(url, headers=LG_HEADERS).json()
        data = r.get('data', [])
        leads.extend(data)
        
        next_token = r.get('nextToken')
        url = f"https://api.leadgenius.app/api/automation/leads?client_id={CLIENT_ID}&limit=500&nextToken={next_token}" if next_token else None

    print(f"  ✅ Total Leads Fetched: {len(leads)}")
    return leads

def upsert_hubspot_contacts(leads):
    print("\n--- Upserting into HubSpot ---")
    
    # DEDUPLICATE BY EMAIL Local
    unique_leads = {}
    for lead in leads:
        email = safe_str(lead.get('email')).lower()
        if not email or email == 'n/a': continue
        
        # We overwrite with the latest processed lead assuming it has the richest data
        # Or better, we only update if the new lead has more fields
        if email not in unique_leads or (lead.get('ai1') and not unique_leads[email].get('ai1')):
            unique_leads[email] = lead
            
    filtered_leads = list(unique_leads.values())
    print(f"  ✅ Distinct emails ready for upload: {len(filtered_leads)} (removed {len(leads) - len(filtered_leads)} duplicates/blanks)")

    batch_size = 100
    for i in range(0, len(filtered_leads), batch_size):
        chunk = filtered_leads[i:i+batch_size]
        inputs = []
        for lead in chunk:
            inputs.append({
                "idProperty": "email",
                "id": safe_str(lead.get('email')).lower(),
                "properties": {
                    "firstname": safe_str(lead.get('firstName')),
                    "lastname": safe_str(lead.get('lastName')) or "Unknown",
                    "jobtitle": safe_str(lead.get('title')),
                    "company": safe_str(lead.get('companyName')),
                    "phone": safe_str(lead.get('phone')),
                    "lg_linkedin_url": safe_str(lead.get('linkedinUrl')),
                    "lg_lead_id": safe_str(lead.get('id')),
                    "lg_ai1": safe_str(lead.get('ai1'))[:65000],
                    "lg_ai2": safe_str(lead.get('ai2'))[:65000],
                    "lg_ai3": safe_str(lead.get('ai3'))[:65000]
                }
            })
            
        r = requests.post('https://api.hubapi.com/crm/v3/objects/contacts/batch/upsert', headers=HS_HEADERS, json={"inputs": inputs})
        if r.status_code in [200, 201, 204]:
            print(f"  ✅ Batch {i} to {i+len(chunk)} upserted ({len(inputs)} unique).")
        else:
            print(f"  ❌ Batch error: {r.status_code} - {r.text[:200]}")

if __name__ == "__main__":
    leads = fetch_all_lg_leads()
    upsert_hubspot_contacts(leads)
