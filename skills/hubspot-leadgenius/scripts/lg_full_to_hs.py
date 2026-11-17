"""
LeadGenius → HubSpot FULL Import
Fetches ALL leads with ALL fields from the individual lead endpoint,
creates comprehensive HubSpot properties, and imports everything.
"""
import requests, os, sys, time, json
from dotenv import load_dotenv

load_dotenv()
HS_TOKEN = os.getenv('HUBSPOT_API_KEY')
LG_TOKEN = os.getenv('LGP_API_KEY')
LG_MASTER = os.getenv('LGP_MASTER_KEY')

if not HS_TOKEN or not LG_TOKEN:
    print("❌ Missing HUBSPOT_API_KEY or LGP_API_KEY in .env")
    sys.exit(1)

HS_HEADERS = {'Authorization': f"Bearer {HS_TOKEN}", 'Content-Type': 'application/json'}
LG_HEADERS = {'X-API-Key': LG_TOKEN}
if LG_MASTER: 
    LG_HEADERS['X-Admin-Key'] = LG_MASTER

CLIENT_ID = "6eceb43b-5c1a-4c4d-898c-36e67b24fdc6"

# ─── HubSpot Custom Properties ───────────────────────────────────────
PROPERTIES = [
    # AI Scoring
    {"name": "lg_ai_score", "label": "LG AI Score", "type": "number", "fieldType": "number", "groupName": "leadgenius_data"},
    {"name": "lg_lead_score", "label": "LG Lead Score", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_qualification", "label": "LG Qualification", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_justification", "label": "LG Score Justification", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_recommendation", "label": "LG Score Recommendation", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_next_action", "label": "LG Next Action", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_likely_engage", "label": "LG Likely to Engage", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_decision_role", "label": "LG Decision Maker Role", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_interest", "label": "LG Interest", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_sentiment", "label": "LG Sentiment", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_nurturing_stage", "label": "LG Nurturing Stage", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_product_fit_score", "label": "LG Product Fit Score", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_risk_score", "label": "LG Risk Score", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_budget_estimation", "label": "LG Budget Estimation", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_purchase_window", "label": "LG Purchase Window", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_engagement_level", "label": "LG Engagement Level", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_engagement_score", "label": "LG Engagement Score", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_social_engagement", "label": "LG Social Engagement", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_competitor_analysis", "label": "LG Competitor Analysis", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    # AI Emails
    {"name": "lg_cold_email", "label": "LG Cold Email", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_linkedin_connect", "label": "LG LinkedIn Connect", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai1", "label": "LG AI 1", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai2", "label": "LG AI 2", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_ai3", "label": "LG AI 3", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    # Enrichment
    {"name": "lg_linkedin_url", "label": "LG LinkedIn URL", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_company_linkedin", "label": "LG Company LinkedIn", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_seniority", "label": "LG Seniority", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_departments", "label": "LG Departments", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_headline", "label": "LG LinkedIn Headline", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_lead_id", "label": "LG Lead ID", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_enrichment_source", "label": "LG Enrichment Source", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_lead_source", "label": "LG Lead Source", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_status", "label": "LG Status", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    # Company
    {"name": "lg_company_url", "label": "LG Company URL", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_company_domain", "label": "LG Company Domain", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_company_analysis", "label": "LG Company Analysis", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_value_proposition", "label": "LG Value Proposition", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_company_value_prop", "label": "LG Company Value Prop", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_company_description", "label": "LG Company Description", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_employees", "label": "LG Employees", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_technologies", "label": "LG Technologies", "type": "string", "fieldType": "textarea", "groupName": "leadgenius_data"},
    {"name": "lg_financials", "label": "LG Financials", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
    {"name": "lg_lead_qualify", "label": "LG Lead Qualify", "type": "string", "fieldType": "text", "groupName": "leadgenius_data"},
]

def safe(val, mx=65000):
    if val is None: return ""
    s = str(val).strip()
    if s in ('N/A', 'None', 'null', ''): return ""
    return s[:mx]

def safe_num(val):
    if val is None: return ""
    try: return str(int(float(val)))
    except: return ""

# ─── STEP 1: Setup HubSpot Properties ──────────────────────────────
def setup_properties():
    print("═══ STEP 1: Setting up HubSpot Properties ═══")
    # Create group
    r = requests.post('https://api.hubapi.com/crm/v3/properties/contacts/groups',
                      headers=HS_HEADERS,
                      json={"name": "leadgenius_data", "displayOrder": -1, "label": "LeadGenius AI Data"})
    if r.status_code == 201: print("  ✅ Property group created")
    else: print("  ⏭️  Property group exists")

    created = skipped = 0
    for prop in PROPERTIES:
        r = requests.post('https://api.hubapi.com/crm/v3/properties/contacts', headers=HS_HEADERS, json=prop)
        if r.status_code == 201: created += 1
        else: skipped += 1
    print(f"  ✅ Properties: {created} created, {skipped} already exist")

# ─── STEP 2: Fetch all lead IDs from list endpoint ─────────────────
def fetch_lead_ids():
    print("\n═══ STEP 2: Fetching lead IDs ═══")
    ids = []
    url = f"https://api.leadgenius.app/api/automation/leads?client_id={CLIENT_ID}&limit=500"
    page = 1
    while url:
        print(f"  ⬇️ Fetching chunk {page}...")
        try:
            r = requests.get(url, headers=LG_HEADERS, timeout=20)
            data = r.json()
            items = data.get('data', [])
            for lead in items:
                ids.append(lead['id'])
            
            print(f"     ✅ Got {len(items)} items")
            next_token = data.get('nextToken')
            url = f"https://api.leadgenius.app/api/automation/leads?client_id={CLIENT_ID}&limit=500&nextToken={next_token}" if next_token else None
            page += 1
        except Exception as e:
            print(f"  ❌ Error fetching IDs: {e}")
            break
            
    print(f"  ✅ Total Found {len(ids)} lead IDs")
    return ids

# ─── STEP 3: Fetch full details for each lead ──────────────────────
def fetch_full_leads(lead_ids):
    print(f"\n═══ STEP 3: Fetching full details for {len(lead_ids)} leads ═══")
    cache_file = '/tmp/lg_full_leads_cache.json'

    # Resume from cache if exists
    cached = {}
    if os.path.exists(cache_file):
        cached = {l['id']: l for l in json.load(open(cache_file))}
        print(f"  📦 Loaded {len(cached)} from cache")

    leads = list(cached.values())
    remaining = [lid for lid in lead_ids if lid not in cached]
    print(f"  🔄 Need to fetch {len(remaining)} remaining leads")

    for i, lid in enumerate(remaining):
        try:
            r = requests.get(f"https://api.leadgenius.app/api/automation/leads/{lid}", headers=LG_HEADERS)
            resp = r.json()
            if resp.get('data', {}).get('id'):
                leads.append(resp.get('data'))
            else:
                # Rate limited or error
                if 'Rate limit' in str(resp) or r.status_code == 429:
                    print(f"\n  ⚠️  Rate limited at {i+1}/{len(remaining)} — waiting 5s (fallback)...")
                    time.sleep(5)
                    r = requests.get(f"https://api.leadgenius.app/api/automation/leads/{lid}", headers=LG_HEADERS)
                    resp = r.json()
                    if resp.get('data', {}).get('id'):
                        leads.append(resp.get('data'))
        except Exception as e:
            print(f"\n  ❌ Error fetching {lid}: {e}")

        if (i+1) % 50 == 0:
            print(f"  ⬇️  Fetched {i+1}/{len(remaining)} (total: {len(leads)})")
            # Save cache periodically
            json.dump(leads, open(cache_file, 'w'))

        time.sleep(0.01)

    # Final cache save
    json.dump(leads, open(cache_file, 'w'))
    print(f"  ✅ Total leads with full data: {len(leads)}")
    return leads

# ─── STEP 4: Parse capture_all for extra fields ────────────────────
def parse_capture_all(capture_all_str):
    """Extract structured fields from the capture_all text dump"""
    result = {}
    if not capture_all_str: return result
    parts = str(capture_all_str).split(' | ')
    for part in parts:
        part = part.strip()
        if part.startswith(':') and ':' in part[1:]:
            key_val = part[1:].split(':', 1)
            if len(key_val) == 2:
                key = key_val[0].strip()
                val = key_val[1].strip()
                if val and val not in ('', 'N/A'):
                    result[key] = val
    return result

def clean_html(text):
    if not text: return ""
    text = text.replace('<br>', '\n').replace('<br/>', '\n').replace('<br />', '\n')
    text = text.replace('\\n', '\n')
    return text.strip()

def parse_email_json(text):
    if not text: return ""
    text = str(text)
    if text.startswith('{'):
        try:
            parsed = json.loads(text)
            subj = parsed.get("subject", "")
            body = parsed.get("content", "")
            if subj and body:
                return f"Subject: {subj}\n\n{clean_html(body)}"
            elif body:
                return clean_html(body)
        except:
            pass
    return clean_html(text)

# ─── STEP 5: Build HubSpot contact from full lead ──────────────────
def build_hs_contact(lead):
    """Map a full LeadGenius lead to HubSpot properties"""
    # Parse capture_all for extra data (phone, technologies, financials, etc.)
    extra = parse_capture_all(lead.get('capture_all', ''))

    # Phone: try phoneNumber first, then sanitizedPhoneNumber, then capture_all fields
    phone = safe(lead.get('phoneNumber')) or safe(lead.get('sanitizedPhoneNumber'))
    if not phone:
        phone = extra.get('Mobile', '') or extra.get('Direct', '') or extra.get('Office', '') or extra.get('HQ', '')

    props = {
        # Standard HubSpot fields
        "firstname": safe(lead.get('firstName')),
        "lastname": safe(lead.get('lastName')) or "Unknown",
        "jobtitle": safe(lead.get('title')),
        "company": safe(lead.get('companyName')),
        "phone": safe(extra.get('Office', '') or extra.get('HQ', '')),
        "mobilephone": safe(extra.get('Mobile', '') or extra.get('Direct', '') or lead.get('phoneNumber') or lead.get('sanitizedPhoneNumber')),
        "city": safe(lead.get('city')) or safe(extra.get('City')),
        "state": safe(lead.get('state')) or safe(extra.get('State')),
        "country": safe(lead.get('country')),
        "industry": safe(lead.get('industry')) or safe(extra.get('Industries')),
        "website": safe(lead.get('companyUrl')) or safe(extra.get('Website')),
    }

    ai_score_val = safe_num(lead.get('aiScoreValue'))
    lg_justification = safe(lead.get('aiScoreJustification'))
    lg_recommendation = safe(lead.get('aiScoreRecommendation'))
    
    ai_lead_score_raw = safe(lead.get('aiLeadScore'))
    if ai_lead_score_raw and ai_lead_score_raw.startswith('{'):
        try:
            parsed = json.loads(ai_lead_score_raw)
            if 'ai_score' in parsed and not ai_score_val:
                ai_score_val = safe_num(parsed.get('ai_score'))
            if 'justification' in parsed:
                lg_justification = parsed.get('justification', '').replace('\\n', '\n').strip()
            if 'recommandation' in parsed:
                lg_recommendation = parsed.get('recommandation', '').replace('\\n', '\n').strip()
        except:
            pass

    props.update({
        # AI Scoring
        "lg_ai_score": ai_score_val,
        "lg_lead_score": ai_lead_score_raw,
        "lg_qualification": safe(lead.get('aiQualification')),
        "lg_justification": lg_justification,
        "lg_recommendation": lg_recommendation,
        "lg_next_action": safe(lead.get('aiNextAction')),
        "lg_likely_engage": safe(lead.get('isLikelyToEngage')),
        "lg_decision_role": safe(lead.get('aiDecisionMakerRole')),
        "lg_interest": safe(lead.get('aiInterest')),
        "lg_sentiment": safe(lead.get('aiSentiment')),
        "lg_nurturing_stage": safe(lead.get('aiNurturingStage')),
        "lg_product_fit_score": safe(lead.get('aiProductFitScore')),
        "lg_risk_score": safe(lead.get('aiRiskScore')),
        "lg_budget_estimation": safe(lead.get('aiBudgetEstimation')),
        "lg_purchase_window": safe(lead.get('aiPurchaseWindow')),
        "lg_engagement_level": safe(lead.get('aiEngagementLevel')),
        "lg_engagement_score": safe(lead.get('engagementScore')),
        "lg_social_engagement": safe(lead.get('aiSocialEngagement')),
        "lg_competitor_analysis": safe(lead.get('aiCompetitorAnalysis')),

        # AI Emails
        "lg_cold_email": parse_email_json(lead.get('aiColdEmail')),
        "lg_linkedin_connect": parse_email_json(lead.get('aiLinkedinConnect')),
        "lg_ai1": parse_email_json(lead.get('ai1')),
        "lg_ai2": parse_email_json(lead.get('ai2')),
        "lg_ai3": parse_email_json(lead.get('ai3')),

        # Enrichment
        "lg_linkedin_url": safe(lead.get('linkedinUrl')),
        "lg_company_linkedin": safe(lead.get('companyLinkedinUrl')) or safe(extra.get('Company Linkedin URL')),
        "lg_seniority": safe(lead.get('seniority')) or safe(extra.get('Seniority')),
        "lg_departments": safe(lead.get('departments')),
        "lg_headline": safe(lead.get('headline')),
        "lg_lead_id": safe(lead.get('id')),
        "lg_enrichment_source": safe(lead.get('enrichmentSource')),
        "lg_lead_source": safe(lead.get('leadSource')),
        "lg_status": safe(lead.get('status')),

        # Company
        "lg_company_url": safe(lead.get('companyUrl')) or safe(extra.get('Website')),
        "lg_company_domain": safe(lead.get('companyDomain')),
        "lg_company_analysis": safe(lead.get('companyAnalysisResult')),
        "lg_value_proposition": safe(lead.get('valueProposition')),
        "lg_company_value_prop": safe(lead.get('companyValueProp')),
        "lg_company_description": safe(extra.get('Company Description')),
        "lg_employees": safe(lead.get('estimatedNumEmployees')) or safe(extra.get('Headcount')),
        "lg_technologies": safe(extra.get('Technologies')),
        "lg_financials": safe(extra.get('Financials')),
        "lg_lead_qualify": safe(lead.get('leadQualify')),
    })

    # Remove empty values
    return {k: v for k, v in props.items() if v}

# ─── STEP 6: Upsert to HubSpot ─────────────────────────────────────
def upsert_to_hubspot(leads):
    print(f"\n═══ STEP 4: Upserting {len(leads)} leads to HubSpot ═══")

    # Split into: leads WITH email (batch upsert by email) and WITHOUT email (individual create)
    with_email = []
    without_email = []
    seen_emails = set()

    for lead in leads:
        email = safe(lead.get('email')).lower()
        if email and email != 'n/a' and email not in seen_emails:
            seen_emails.add(email)
            with_email.append(lead)
        else:
            without_email.append(lead)

    print(f"  📧 With email: {len(with_email)} | 🔒 Without email: {len(without_email)}")

    # ─── Batch upsert leads WITH email ────────────────
    print(f"\n  --- Batch upserting {len(with_email)} contacts by email ---")
    batch_size = 100
    batch_ok = 0
    batch_err = 0
    for i in range(0, len(with_email), batch_size):
        chunk = with_email[i:i+batch_size]
        inputs = []
        for lead in chunk:
            props = build_hs_contact(lead)
            email = safe(lead.get('email')).lower()
            inputs.append({"idProperty": "email", "id": email, "properties": props})

        r = requests.post('https://api.hubapi.com/crm/v3/objects/contacts/batch/upsert',
                          headers=HS_HEADERS, json={"inputs": inputs})
        if r.status_code in [200, 201]:
            batch_ok += len(inputs)
            print(f"  ✅ Batch {i}-{i+len(chunk)}: {len(inputs)} upserted")
        else:
            batch_err += len(inputs)
            print(f"  ❌ Batch {i}-{i+len(chunk)}: {r.text[:200]}")
        time.sleep(0.2)

    print(f"  📊 Email batch: {batch_ok} OK, {batch_err} errors")

    # ─── Create leads WITHOUT email individually ──────
    print(f"\n  --- Creating {len(without_email)} contacts without email ---")
    create_ok = 0
    create_err = 0
    create_skip = 0
    for i, lead in enumerate(without_email):
        props = build_hs_contact(lead)
        # Must have at least a name or company
        if not props.get('firstname') and not props.get('lastname', '') != 'Unknown':
            create_skip += 1
            continue

        r = requests.post('https://api.hubapi.com/crm/v3/objects/contacts',
                          headers=HS_HEADERS, json={"properties": props})
        if r.status_code in [200, 201]:
            create_ok += 1
        else:
            # May be duplicate by other criteria — skip gracefully
            create_err += 1
            if create_err <= 3:
                print(f"  ⚠️  {props.get('firstname','')} {props.get('lastname','')}: {r.text[:120]}")

        if (i+1) % 50 == 0:
            print(f"  🔄 Created {create_ok}/{i+1} (errors: {create_err})")
        time.sleep(0.12)  # HubSpot rate limit: ~10/sec

    print(f"  📊 No-email: {create_ok} created, {create_err} errors, {create_skip} skipped")

    print(f"\n═══ IMPORT COMPLETE ═══")
    print(f"  Total leads processed: {len(leads)}")
    print(f"  Email upserts: {batch_ok}")
    print(f"  No-email creates: {create_ok}")
    print(f"  Errors: {batch_err + create_err}")

# ─── MAIN ───────────────────────────────────────────────────────────
if __name__ == "__main__":
    setup_properties()
    lead_ids = fetch_lead_ids()
    leads = fetch_full_leads(lead_ids)
    upsert_to_hubspot(leads)
