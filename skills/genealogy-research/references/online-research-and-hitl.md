# Online Research & Human-in-the-Loop

## FamilySearch (familysearch.org)

Two distinct parts:
1. **The Tree** — collaborative family tree (anyone can edit, quality varies)
2. **Historical Records** — digitized/indexed records from archives worldwide

### API Access

```python
import requests

def fs_get(endpoint, token, params=None):
    headers = {
        "Authorization": f"Bearer {token}",  # fssessionid cookie value
        "Accept": "application/json"
    }
    return requests.get(
        f"https://api.familysearch.org{endpoint}",
        headers=headers, params=params
    ).json()

person = fs_get(f"/platform/tree/persons/{pid}", token)
ancestry = fs_get("/platform/tree/ancestry", token, {"person": pid, "generations": 4})
results = fs_get("/platform/tree/search", token,
                  {"q": 'surname:"Silva" givenName:"Antonio" birthLikePlace:"Botucatu"'})
```

**Token**: Browser DevTools → Application → Cookies → `fssessionid`. Lasts ~24h. Send as `Authorization: Bearer {token}`, NOT as Cookie header.

### Search Tips
- Search with name variants (Giuseppe AND José, Müller AND Muller)
- `birthLikePlace` with broadest useful area (city, not street)
- `birthLikeDate` with range: `"1895-1905"`
- Check **sources** tab — attached records are more reliable than tree data
- Check **change log** — reliable contributors are gold

### Key Collections by Region

FamilySearch organizes records by country and state/province. Start by searching for "[Country], [Region]" in the catalog.

**General availability**:
- Most European countries have civil registration from the mid-1800s
- Church records (baptism, marriage, burial) often go back centuries earlier
- Not all collections are indexed — many are **image-only** (browse page by page)

## Other Online Sources

| Source | Best For | Access |
|---|---|---|
| **Ancestry** (ancestry.com) | US/UK/Canadian records, immigration, census | Paid (human browses) |
| **Geneanet** (geneanet.org) | Finding other researchers, European trees | Free, blocks bots |
| **Antenati** (antenati.cultura.gov.it) | Italian state archives | Free |
| **CEPESE** (cepese.pt) | Portuguese emigration records | Free |
| **Geneteka** (geneteka.genealodzy.pl) | Polish parish record index | Free |
| **Archion** (archion.de) | German Protestant church records | Subscription |
| **Matricula** (data.matricula-online.eu) | German/Austrian Catholic records | Free |
| **FindMyPast** (findmypast.com) | UK/Irish records | Paid |
| Find A Grave, BillionGraves | Cemetery records with photos | Free |
| Newspapers (various archives) | Obituaries, announcements, legal notices | Varies |
| Forebears.io | Surname distribution worldwide | Free |
| MyHeritage | DNA matching, some unique records | Freemium |

### Blog and Local History Research

For many countries, local history blogs and genealogy forums are MORE useful than large databases. Adapt search patterns to the family's language and region:

```
"[surname]" "[city]" genealogy
"[surname]" "[city]" family history
"[full name]" birth OR death OR marriage certificate
"[full name]" obituary
"[city]" "family history"
```

When you find a relevant blog: read it thoroughly, extract names/dates/relationships, note the author (potential research ally), **save the content** (blogs disappear — archive or note Wayback Machine URL).

### Surname Distribution

Check before deep-diving: Forebears.io (global). A rare surname is a research advantage — any hit is likely family. A common surname needs more filters (place, date, parents' names).

---

## Human-in-the-Loop

### When to Involve the Human

**Agent handles**: OCR, database searches, YAML management, journal updates, web scraping of public sites, data analysis, cross-referencing, draft writing.

**Human handles**: phone calls to relatives, archive visits, civil registry requests, solving CAPTCHAs, paying for certificates, making judgment calls about relationships, interpreting old handwriting, emotional/sensitivity decisions.

### Crafting Questions for Relatives

Number every question. Group by topic. Start with easy/pleasant questions. For elderly relatives: max 10-15 questions per session. Accept any response format.

```
About [Person Name]:
1. What was their full name (including middle names)?
2. When were they born (or approximate year)?
3. Where were they born (city, state/province, country)?
4. When and where did they die?
5. Who were their parents? (full names if possible)
6. Who were their siblings? (names, birth order if known)
7. What did they do for a living?
8. Where did they live during their life?

About the family:
9. Where did the family originally come from?
10. When did they arrive in [current country/region]?
11. Are there any old documents, photos, or letters in the family?
12. Is there anyone who knows more about the family history?
```

After receiving answers: transcribe immediately, extract to YAMLs, journal the contact, generate follow-up questions, mark confidence as `medium` (oral).

### Civil Registry Requests

Many civil registries worldwide respond to written or email requests. When preparing one:

- Include the person's **full name** and **parents' names** (this is how registrars search their books)
- Provide a **date range** if the exact date is uncertain
- State it's for genealogical/family history research
- Be polite and concise — registrars are busy
- Expect fees per certificate (varies by country and jurisdiction)
- The human must send the request — prepare it, let them handle communication

Adapt the language and formality to the country. In some countries, requests can be made online; in others, you must write a formal letter.

### Handling Blocked Sites

Prepare a brief for the human:

```
I need data from [SITE] but it blocks automated access.
Could you please:
1. Go to [EXACT URL]
2. Search for: [EXACT TERMS]
3. I'm looking for: [WHAT SPECIFICALLY]
4. Please: [screenshot / copy text / note reference number]
This should take about [X] minutes.
```

Sites commonly needing human intervention: FamilySearch (hCaptcha), Geneanet (bot blocking), Ancestry (paywall + bot detection), various national archives with JavaScript-heavy rendering.

### Browser Automation for Image-Only Collections

For browsing unindexed collections (image-only microfilm), you may need browser automation:

```python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch(headless=False)  # MUST be headed (hCaptcha)
    context = browser.new_context(storage_state="auth-state.json")
    page = context.new_page()
    # Human solves CAPTCHA once, save state, reuse
```

Always use headed mode. Have the human solve the CAPTCHA once, save the browser state, and reuse it.

### Research Brief Template

When you need the human to do something, be specific and efficient:

```markdown
## Research Task: [Title]
**Priority**: High / Medium / Low
**Estimated time**: X minutes
**What I need**: [Specific data]
**Steps:**
1. Go to [URL] / Call [number] / Visit [place]
2. Search for [exact terms]
3. Looking for [specific information]
**Context**: [Why this matters — connects to which ancestor, resolves which conflict]
```

### Tracking Research Across Multiple Branches

When the tree gets large (50+ people):
1. Use YAML flags consistently — search for `NEEDS_RESEARCH` across all YAMLs
2. Prioritize by generation — closer generations first (they unlock farther ones)
3. Track blocked branches — waiting for a registry response, a relative's callback
4. Keep TODO.md updated — it's the project dashboard
5. Review journal periodically — patterns emerge
