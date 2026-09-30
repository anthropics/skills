# Instagram API Automation Setup Guide

Complete step-by-step guide to set up Instagram Graph API automation for @teamsandhu3.

---

## Prerequisites

- Instagram Business Account (not personal account)
- Meta Business Manager access
- Python 3.8+ installed
- Instagram Graph API access approval from Meta

---

## Step 1: Convert to Instagram Business Account

If your account is personal:

1. Go to **Settings → Account Type**
2. Click "Switch to Professional Account"
3. Select "Business"
4. Connect a Facebook Page (create one if needed)

**Why:** Only Business accounts can use the Instagram Graph API for scheduling and publishing.

---

## Step 2: Get Your Access Token

### Option A: Get Long-Lived Access Token (Recommended)

1. Go to [Meta Business Suite](https://business.facebook.com)
2. Navigate to **Settings → Business Settings**
3. Go to **Users → Your Name**
4. Scroll to "Access Tokens"
5. Click "Generate Token"
6. Select the permissions:
   - `instagram_basic`
   - `instagram_content_publishing`
   - `instagram_manage_insights`
   - `pages_read_engagement`
7. Copy the generated token (this is your `INSTAGRAM_ACCESS_TOKEN`)

### Option B: Get Token via Graph API Explorer

1. Go to [Graph API Explorer](https://developers.facebook.com/tools/explorer)
2. Select your app from dropdown
3. Click "Get Token"
4. Choose "Get Access Token"
5. Select permissions (see above)
6. Generate and copy token

**Token Validity:**
- Short-lived: 1 hour
- Long-lived: 60 days
- Server-to-server: Can refresh indefinitely

---

## Step 3: Get Your Business Account ID

1. Go to [Meta Business Suite](https://business.facebook.com)
2. Click your name in top-left
3. Go to **Accounts → Instagram Accounts**
4. Find your account and click it
5. Copy the ID from the URL: `https://business.instagram.com/accounts/ACCOUNT_ID/`
6. Or use the Graph API Explorer:

```bash
curl "https://graph.instagram.com/me?fields=id,username&access_token=YOUR_ACCESS_TOKEN"
```

---

## Step 4: Set Up Environment Variables

Create `.env` file in your project directory:

```bash
# .env
INSTAGRAM_ACCESS_TOKEN=your_token_here
INSTAGRAM_BUSINESS_ACCOUNT_ID=your_account_id_here
```

**Security:** Never commit `.env` to git. Add to `.gitignore`:

```
.env
instagram_analytics.db
*.log
```

---

## Step 5: Install Dependencies

```bash
pip install -r requirements.txt
```

Or install manually:

```bash
pip install requests==2.31.0 python-dotenv==1.0.0
```

---

## Step 6: Test the Setup

```bash
# Test your credentials
python instagram_automation.py account
```

Expected output:
```json
{
  "id": "your_account_id",
  "name": "Your Name",
  "username": "teamsandhu3",
  "biography": "Your bio",
  "followers_count": 1234,
  "follows_count": 567,
  "website": "your-website.com",
  "profile_picture_url": "https://..."
}
```

If you see errors, verify:
- [ ] Access token is correct and not expired
- [ ] Business account ID is correct
- [ ] Account is Business type (not Personal)
- [ ] Permissions are granted

---

## Step 7: Schedule Automation

### On macOS/Linux (Cron)

1. Open terminal
2. Run `crontab -e`
3. Add these lines:

```bash
# Run daily automation at 9 AM IST (3:30 AM UTC)
30 3 * * * cd /path/to/project && python instagram_automation.py daily >> instagram_automation.log 2>&1

# Check for posts to publish every 30 minutes
*/30 * * * * cd /path/to/project && python instagram_automation.py daily >> instagram_automation.log 2>&1
```

4. Save and exit

### On Windows (Task Scheduler)

1. Press `Win + R`, type `taskschd.msc`
2. Click "Create Basic Task"
3. Name: "Instagram Daily Automation"
4. Set trigger: Daily at 9 AM
5. Set action:
   - Program: `python.exe`
   - Arguments: `C:\path\to\instagram_automation.py daily`
   - Start in: `C:\path\to\`
6. Click OK

### Using Python Schedule (Alternative)

```python
import schedule
import time
from instagram_automation import DailyAutomation

automation = DailyAutomation()

# Schedule tasks
schedule.every().day.at("09:00").do(automation.run_daily_tasks)
schedule.every(30).minutes.do(automation.scheduler.check_and_publish)

# Keep running
while True:
    schedule.run_pending()
    time.sleep(60)
```

Run this script and keep it running:
```bash
python schedule_runner.py
```

---

## Usage Guide

### Schedule a Post

```bash
python instagram_automation.py schedule \
  "Day 1 Reel" \
  "Husband Wife Reality Check - Do couples really match? 👀 #couple #trending" \
  "https://example.com/video.mp4" \
  "VIDEO" \
  "2026-08-07T09:00:00"
```

Or programmatically:

```python
from instagram_automation import DailyAutomation
from datetime import datetime, timedelta

automation = DailyAutomation()

scheduled_time = datetime.now() + timedelta(days=1, hours=1)

automation.scheduler.schedule_post(
    title="Day 1 Reel",
    caption="Husband Wife Reality Check - Do couples really match? 👀",
    media_url="https://example.com/video.mp4",
    media_type="VIDEO",
    scheduled_time=scheduled_time,
    hashtags="#couple #trending #reels #couples2024 #hungarianwife #punjabihusband"
)
```

### Run Daily Tasks

```bash
python instagram_automation.py daily
```

This will:
1. Check and publish scheduled posts
2. Update analytics for recent media
3. Generate daily report
4. Export analytics to CSV

### Generate Report

```bash
python instagram_automation.py report
```

Output: JSON with top posts and analytics

### Export Analytics

```bash
python instagram_automation.py export analytics.csv
```

### Get Account Info

```bash
python instagram_automation.py account
```

---

## Database Schema

The automation creates SQLite database with these tables:

### `media_analytics`
Tracks each post's performance:
- ID, Caption, Media Type, Published Date
- Like count, Comment count, Impressions, Reach
- Saved count, Video views, Engagement rate

### `daily_metrics`
Daily account-level metrics:
- Followers, Impressions, Reach, Profile views
- New followers, Total engagement

### `scheduled_posts`
Posts pending publication:
- Title, Caption, Media URL, Media type
- Scheduled time, Status (scheduled/posted/failed)

### `sponsorships`
Brand partnership tracking:
- Brand name, Email, Status, Rate
- Content delivered, Payment received

---

## API Permissions Explained

| Permission | Purpose |
|-----------|---------|
| `instagram_basic` | Read basic account info |
| `instagram_content_publishing` | Publish posts, reels, stories |
| `instagram_manage_insights` | Get analytics/insights data |
| `pages_read_engagement` | Read likes, comments, shares |
| `pages_manage_engagement` | Respond to comments/DMs |
| `business_management` | Access business features |

---

## Posting Limits

**Instagram Rate Limits:**
- Max 10 posts per 24 hours (per account)
- Stories: Unlimited but practical limit is 30-50/day
- Reels: Count as regular posts (10 per 24h)

**Best Practices:**
- Spread posts throughout the day
- 3-4 posts per day maximum
- Wait 1-2 hours between posts
- Avoid posting during off-hours

---

## Troubleshooting

### "Invalid access token"
- Token expired (short-lived tokens last 1 hour)
- Token revoked in Meta Business settings
- Solution: Generate new long-lived token

### "Invalid Instagram account ID"
- Account ID is incorrect
- Account doesn't exist
- Solution: Verify ID from Meta Business Suite

### "Permission denied" error
- Missing required permissions in token
- Business account not connected to token
- Solution: Regenerate token with all permissions

### "Rate limit exceeded"
- Too many API calls in short time
- Solution: Add delays between requests (script does this automatically)

### Posts not publishing
- Video file corrupted
- Caption contains banned words/links
- Media URL expired/inaccessible
- Solution: Check logs in `instagram_automation.log`

### Database locked error
- Script running twice simultaneously
- Previous script crashed without cleanup
- Solution: Wait 30 seconds, try again

---

## Advanced: API Request Examples

### Upload Image

```python
api = InstagramAPI(ACCESS_TOKEN, BUSINESS_ACCOUNT_ID)

result = api.upload_and_publish_image(
    image_url="https://example.com/image.jpg",
    caption="Check out this amazing content! #trending"
)

print(result['id'])  # Media ID if successful
```

### Get Media Insights

```python
media_id = "12345678"
insights = api.get_media_insights(media_id)

for metric in insights['data']:
    print(f"{metric['name']}: {metric['values'][0]['value']}")

# Output:
# engagement: 234
# impressions: 5600
# reach: 3200
# saved: 45
```

### Create Media Container

```python
# For images
container = api.make_request(
    f"{BUSINESS_ACCOUNT_ID}/media",
    method='POST',
    data={
        'image_url': 'https://example.com/image.jpg',
        'caption': 'Your caption here',
        'user_tags': []
    }
)

media_id = container['id']

# Then publish
publish = api.make_request(
    f"{BUSINESS_ACCOUNT_ID}/media_publish",
    method='POST',
    data={'creation_id': media_id}
)
```

---

## Analytics Tracking

### View Database Directly

```bash
sqlite3 instagram_analytics.db

# List all tables
.tables

# View top posts
SELECT caption, like_count, comment_count, engagement_rate 
FROM media_analytics 
ORDER BY engagement_rate DESC 
LIMIT 10;

# Exit
.quit
```

### Generate Custom Reports

```python
db = AnalyticsDatabase()

# Get last 30 days
recent = db.get_daily_analytics(30)
for day in recent:
    print(f"{day['date']}: {day['followers']} followers, {day['engagement']} engagement")

# Get top 20 posts
top = db.get_top_posts(20)
for post in top:
    print(f"{post['caption']}: {post['engagement_rate']:.2f}% engagement")
```

---

## 15-Day Posting Schedule

### Pre-populate scheduled posts:

```python
from datetime import datetime, timedelta
from instagram_automation import DailyAutomation

automation = DailyAutomation()

# Day 1 - Hook Phase (9 AM)
base_time = datetime(2026, 8, 7, 9, 0, 0)

posts = [
    {
        'title': 'Day 1 - Husband Wife Reality Check',
        'caption': 'Husband Wife Reality Check - Do couples really match? 👀 #couple #trending',
        'media_url': 'https://your-url/day1.mp4',
        'media_type': 'VIDEO',
        'time_offset_hours': 0,
        'hashtags': '#couple #trending #reels #couples2024'
    },
    {
        'title': 'Day 2 - Fitness Transformation',
        'caption': 'Our 90-day fitness transformation 💪 #fitness #transformation',
        'media_url': 'https://your-url/day2.mp4',
        'media_type': 'VIDEO',
        'time_offset_hours': 24,
        'hashtags': '#fitness #fitnesschallenge #transformation'
    },
    # ... continue for all 15 days
]

for post in posts:
    scheduled_time = base_time + timedelta(hours=post['time_offset_hours'])
    automation.scheduler.schedule_post(
        title=post['title'],
        caption=post['caption'],
        media_url=post['media_url'],
        media_type=post['media_type'],
        scheduled_time=scheduled_time,
        hashtags=post['hashtags']
    )
```

---

## Security Best Practices

1. **Never commit `.env` file**
   - Add to `.gitignore`
   - Use environment variables in production

2. **Rotate tokens regularly**
   - Regenerate long-lived tokens monthly
   - Revoke old tokens

3. **Use API rate limiting**
   - Script includes automatic rate limiting
   - Monitor API usage in Meta Business Suite

4. **Secure database**
   - Backup `instagram_analytics.db` regularly
   - Don't share database file
   - Consider encrypting sensitive data

5. **Monitor logs**
   - Check `instagram_automation.log` daily
   - Look for errors or unusual API responses

---

## Next Steps

1. ✅ Get access token and account ID
2. ✅ Set up `.env` file
3. ✅ Install dependencies
4. ✅ Test with `account` command
5. ✅ Schedule 15 posts using templates
6. ✅ Set up daily cron/scheduler
7. ✅ Monitor logs and analytics
8. ✅ Track sponsorship results

---

## Support & Troubleshooting

- Check logs: `tail -f instagram_automation.log`
- Test API: `python instagram_automation.py account`
- View database: `sqlite3 instagram_analytics.db`
- Export analytics: `python instagram_automation.py export`

For API errors, reference [Instagram Graph API Docs](https://developers.facebook.com/docs/instagram-api)
