#!/usr/bin/env python3
"""
Instagram Automation Suite for @teamsandhu3
Handles scheduling, posting, analytics tracking, and engagement monitoring
Requires: Instagram Graph API access and Business Account

Setup:
1. Install dependencies: pip install -r requirements.txt
2. Get your access token from Meta Business Suite
3. Set environment variables: INSTAGRAM_ACCESS_TOKEN, INSTAGRAM_BUSINESS_ACCOUNT_ID
4. Run this script on a schedule (cronjob or similar)
"""

import os
import json
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional
import sqlite3
import logging
from dotenv import load_dotenv
import time

# Load environment variables
load_dotenv()

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('instagram_automation.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Instagram Graph API endpoints
GRAPH_API_VERSION = "v18.0"
GRAPH_API_BASE = f"https://graph.instagram.com/{GRAPH_API_VERSION}"

# Configuration from environment
ACCESS_TOKEN = os.getenv('INSTAGRAM_ACCESS_TOKEN')
BUSINESS_ACCOUNT_ID = os.getenv('INSTAGRAM_BUSINESS_ACCOUNT_ID')
DB_NAME = 'instagram_analytics.db'

if not ACCESS_TOKEN or not BUSINESS_ACCOUNT_ID:
    logger.error("Missing required environment variables: INSTAGRAM_ACCESS_TOKEN, INSTAGRAM_BUSINESS_ACCOUNT_ID")
    raise ValueError("Environment variables not configured")


class InstagramAPI:
    """Handles all Instagram Graph API interactions"""

    def __init__(self, access_token: str, business_account_id: str):
        self.access_token = access_token
        self.business_account_id = business_account_id
        self.headers = {
            'Authorization': f'Bearer {self.access_token}',
            'Content-Type': 'application/json'
        }

    def make_request(self, endpoint: str, method: str = 'GET', data: dict = None) -> dict:
        """Make authenticated request to Instagram Graph API"""
        url = f"{GRAPH_API_BASE}/{endpoint}"

        try:
            if method == 'GET':
                response = requests.get(url, headers=self.headers, params={'access_token': self.access_token})
            elif method == 'POST':
                response = requests.post(url, headers=self.headers, json=data, params={'access_token': self.access_token})
            else:
                raise ValueError(f"Unsupported method: {method}")

            response.raise_for_status()
            return response.json()

        except requests.exceptions.RequestException as e:
            logger.error(f"API request failed: {e}")
            return {'error': str(e)}

    def get_account_info(self) -> dict:
        """Get business account information"""
        endpoint = f"{self.business_account_id}?fields=id,name,username,biography,followers_count,follows_count,website,profile_picture_url"
        return self.make_request(endpoint)

    def get_media_feed(self, limit: int = 20) -> List[dict]:
        """Get recent media from account feed"""
        endpoint = f"{self.business_account_id}/media?fields=id,caption,media_type,media_url,timestamp,like_count,comments_count"
        params = f"{self.business_account_id}/media?fields=id,caption,media_type,media_url,timestamp,like_count,comments_count&limit={limit}"

        # Use direct URL construction for proper parameter handling
        url = f"{GRAPH_API_BASE}/{params}&access_token={self.access_token}"
        try:
            response = requests.get(url)
            response.raise_for_status()
            return response.json().get('data', [])
        except Exception as e:
            logger.error(f"Failed to fetch media feed: {e}")
            return []

    def get_media_insights(self, media_id: str) -> dict:
        """Get detailed insights for a specific media post"""
        endpoint = f"{media_id}/insights?metric=engagement,impressions,reach,saved,video_views,ig_reels_avg_completion_rate_watched_actions"
        return self.make_request(endpoint)

    def upload_and_publish_image(self, image_url: str, caption: str) -> dict:
        """Upload image and publish to feed"""

        # Step 1: Create media container
        container_endpoint = f"{self.business_account_id}/media"
        container_data = {
            'image_url': image_url,
            'caption': caption,
            'user_tags': []
        }

        container_response = self.make_request(container_endpoint, method='POST', data=container_data)

        if 'error' in container_response:
            logger.error(f"Failed to create media container: {container_response}")
            return container_response

        media_id = container_response.get('id')

        # Step 2: Publish the media
        publish_endpoint = f"{self.business_account_id}/media_publish"
        publish_data = {'creation_id': media_id}

        publish_response = self.make_request(publish_endpoint, method='POST', data=publish_data)

        if 'id' in publish_response:
            logger.info(f"Successfully published media: {publish_response['id']}")

        return publish_response

    def upload_and_publish_video(self, video_url: str, thumbnail_url: str, caption: str) -> dict:
        """Upload video/reel and publish"""

        # Create media container for video
        container_endpoint = f"{self.business_account_id}/media"
        container_data = {
            'media_type': 'VIDEO',
            'video_url': video_url,
            'thumbnail_url': thumbnail_url,
            'caption': caption
        }

        container_response = self.make_request(container_endpoint, method='POST', data=container_data)

        if 'error' in container_response:
            logger.error(f"Failed to create video container: {container_response}")
            return container_response

        media_id = container_response.get('id')

        # Publish the video
        publish_endpoint = f"{self.business_account_id}/media_publish"
        publish_data = {'creation_id': media_id}

        publish_response = self.make_request(publish_endpoint, method='POST', data=publish_data)

        if 'id' in publish_response:
            logger.info(f"Successfully published video: {publish_response['id']}")

        return publish_response

    def get_insights_summary(self, date_range_days: int = 7) -> dict:
        """Get account-level insights for date range"""
        endpoint = f"{self.business_account_id}/insights?metric=impressions,reach,profile_views,follower_count"

        start_date = (datetime.now() - timedelta(days=date_range_days)).strftime('%Y-%m-%d')
        end_date = datetime.now().strftime('%Y-%m-%d')

        # Note: Metric-level date filtering requires specific endpoint
        return self.make_request(endpoint)


class AnalyticsDatabase:
    """Handles SQLite database for storing analytics history"""

    def __init__(self, db_name: str = DB_NAME):
        self.db_name = db_name
        self.init_database()

    def init_database(self):
        """Initialize database tables"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        # Media analytics table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS media_analytics (
                id TEXT PRIMARY KEY,
                caption TEXT,
                media_type TEXT,
                published_date TIMESTAMP,
                tracked_date TIMESTAMP,
                like_count INTEGER,
                comment_count INTEGER,
                impressions INTEGER,
                reach INTEGER,
                saved_count INTEGER,
                video_views INTEGER,
                engagement_rate REAL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')

        # Daily account metrics table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS daily_metrics (
                tracking_date DATE PRIMARY KEY,
                followers INTEGER,
                impressions INTEGER,
                reach INTEGER,
                profile_views INTEGER,
                new_followers INTEGER,
                total_engagement INTEGER,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')

        # Scheduled posts table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS scheduled_posts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                title TEXT,
                caption TEXT,
                media_url TEXT,
                media_type TEXT,
                scheduled_time TIMESTAMP,
                posted_time TIMESTAMP,
                status TEXT DEFAULT 'scheduled',
                hashtags TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')

        # Sponsorship tracking table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS sponsorships (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                brand_name TEXT,
                contact_email TEXT,
                status TEXT,
                quoted_rate REAL,
                accepted_rate REAL,
                content_delivered INTEGER,
                payment_received REAL,
                post_ids TEXT,
                negotiation_notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')

        conn.commit()
        conn.close()
        logger.info("Database initialized successfully")

    def add_media_analytics(self, media_id: str, data: dict):
        """Store or update media analytics"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        # Calculate engagement rate
        likes = data.get('like_count', 0)
        comments = data.get('comments_count', 0)
        reach = data.get('reach', 1)
        engagement_rate = ((likes + comments) / reach * 100) if reach > 0 else 0

        cursor.execute('''
            INSERT OR REPLACE INTO media_analytics
            (id, caption, media_type, published_date, tracked_date, like_count, comment_count,
             impressions, reach, saved_count, video_views, engagement_rate, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
        ''', (
            media_id,
            data.get('caption', ''),
            data.get('media_type', 'IMAGE'),
            data.get('timestamp', datetime.now()),
            datetime.now(),
            data.get('like_count', 0),
            data.get('comments_count', 0),
            data.get('impressions', 0),
            data.get('reach', 0),
            data.get('saved_count', 0),
            data.get('video_views', 0),
            engagement_rate
        ))

        conn.commit()
        conn.close()
        logger.info(f"Analytics saved for media {media_id}")

    def add_scheduled_post(self, title: str, caption: str, media_url: str,
                          media_type: str, scheduled_time: datetime, hashtags: str):
        """Add new scheduled post"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            INSERT INTO scheduled_posts
            (title, caption, media_url, media_type, scheduled_time, hashtags)
            VALUES (?, ?, ?, ?, ?, ?)
        ''', (title, caption, media_url, media_type, scheduled_time, hashtags))

        conn.commit()
        post_id = cursor.lastrowid
        conn.close()
        logger.info(f"Scheduled post {post_id}: {title}")
        return post_id

    def get_scheduled_posts(self, status: str = 'scheduled'):
        """Get posts scheduled for posting"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            SELECT id, title, caption, media_url, media_type, scheduled_time, hashtags
            FROM scheduled_posts
            WHERE status = ? AND scheduled_time <= ?
            ORDER BY scheduled_time
        ''', (status, datetime.now()))

        posts = cursor.fetchall()
        conn.close()
        return posts

    def update_post_status(self, post_id: int, status: str, posted_time: datetime = None):
        """Update scheduled post status"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        if posted_time:
            cursor.execute('''
                UPDATE scheduled_posts
                SET status = ?, posted_time = ?
                WHERE id = ?
            ''', (status, posted_time, post_id))
        else:
            cursor.execute('''
                UPDATE scheduled_posts
                SET status = ?
                WHERE id = ?
            ''', (status, post_id))

        conn.commit()
        conn.close()

    def get_daily_analytics(self, days: int = 30) -> List[dict]:
        """Get daily analytics summary"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            SELECT tracking_date, followers, impressions, reach, profile_views,
                   new_followers, total_engagement
            FROM daily_metrics
            WHERE tracking_date >= date('now', ? || ' days')
            ORDER BY tracking_date DESC
        ''', (-days,))

        columns = ['date', 'followers', 'impressions', 'reach', 'profile_views', 'new_followers', 'engagement']
        results = cursor.fetchall()
        conn.close()

        return [dict(zip(columns, row)) for row in results]

    def get_top_posts(self, limit: int = 10) -> List[dict]:
        """Get top-performing posts by engagement"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            SELECT id, caption, media_type, published_date, like_count, comment_count,
                   impressions, reach, engagement_rate
            FROM media_analytics
            ORDER BY engagement_rate DESC
            LIMIT ?
        ''', (limit,))

        columns = ['id', 'caption', 'media_type', 'date', 'likes', 'comments', 'impressions', 'reach', 'engagement_rate']
        results = cursor.fetchall()
        conn.close()

        return [dict(zip(columns, row)) for row in results]

    def add_sponsorship(self, brand_name: str, contact_email: str, quoted_rate: float = 0):
        """Add sponsorship opportunity tracking"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            INSERT INTO sponsorships (brand_name, contact_email, quoted_rate, status)
            VALUES (?, ?, ?, 'prospect')
        ''', (brand_name, contact_email, quoted_rate))

        conn.commit()
        sponsor_id = cursor.lastrowid
        conn.close()
        logger.info(f"Added sponsorship prospect: {brand_name}")
        return sponsor_id

    def update_sponsorship(self, sponsor_id: int, status: str, notes: str = ''):
        """Update sponsorship status"""
        conn = sqlite3.connect(self.db_name)
        cursor = conn.cursor()

        cursor.execute('''
            UPDATE sponsorships
            SET status = ?, negotiation_notes = ?, updated_at = CURRENT_TIMESTAMP
            WHERE id = ?
        ''', (status, notes, sponsor_id))

        conn.commit()
        conn.close()


class PostScheduler:
    """Handles scheduling and automated posting"""

    def __init__(self, api: InstagramAPI, db: AnalyticsDatabase):
        self.api = api
        self.db = db

    def schedule_post(self, title: str, caption: str, media_url: str,
                     media_type: str, scheduled_time: datetime, hashtags: str = ''):
        """Schedule a post for future publishing"""
        post_id = self.db.add_scheduled_post(title, caption, media_url, media_type, scheduled_time, hashtags)
        logger.info(f"Post {post_id} scheduled for {scheduled_time}")
        return post_id

    def check_and_publish(self):
        """Check scheduled posts and publish if time has arrived"""
        scheduled_posts = self.db.get_scheduled_posts()

        for post in scheduled_posts:
            post_id, title, caption, media_url, media_type, scheduled_time, hashtags = post

            # Add hashtags to caption
            if hashtags:
                caption = f"{caption}\n\n{hashtags}"

            try:
                if media_type.upper() == 'VIDEO':
                    result = self.api.upload_and_publish_video(media_url, '', caption)
                else:  # IMAGE
                    result = self.api.upload_and_publish_image(media_url, caption)

                if 'id' in result:
                    self.db.update_post_status(post_id, 'posted', datetime.now())
                    logger.info(f"Successfully published post {post_id}")
                else:
                    logger.error(f"Failed to publish post {post_id}: {result}")
                    self.db.update_post_status(post_id, 'failed')

            except Exception as e:
                logger.error(f"Error publishing post {post_id}: {e}")
                self.db.update_post_status(post_id, 'error')


class AnalyticsTracker:
    """Tracks analytics and generates reports"""

    def __init__(self, api: InstagramAPI, db: AnalyticsDatabase):
        self.api = api
        self.db = db

    def update_media_analytics(self):
        """Fetch and update analytics for all recent media"""
        media_feed = self.api.get_media_feed(limit=20)

        for media in media_feed:
            media_id = media.get('id')

            # Get detailed insights
            insights = self.api.get_media_insights(media_id)

            # Parse insights into useful format
            insight_data = {
                'caption': media.get('caption', ''),
                'media_type': media.get('media_type', 'IMAGE'),
                'timestamp': media.get('timestamp'),
                'like_count': media.get('like_count', 0),
                'comments_count': media.get('comments_count', 0),
            }

            # Extract insights metrics
            for metric in insights.get('data', []):
                metric_name = metric.get('name')
                metric_value = metric.get('values', [{}])[0].get('value', 0)

                if metric_name == 'engagement':
                    insight_data['engagement'] = metric_value
                elif metric_name == 'impressions':
                    insight_data['impressions'] = metric_value
                elif metric_name == 'reach':
                    insight_data['reach'] = metric_value
                elif metric_name == 'saved':
                    insight_data['saved_count'] = metric_value
                elif metric_name == 'video_views':
                    insight_data['video_views'] = metric_value

            # Store in database
            self.db.add_media_analytics(media_id, insight_data)
            time.sleep(0.5)  # Rate limiting

    def generate_daily_report(self):
        """Generate daily performance report"""
        top_posts = self.db.get_top_posts(10)
        daily_analytics = self.db.get_daily_analytics(7)

        report = {
            'generated_at': datetime.now().isoformat(),
            'top_posts': top_posts,
            'last_7_days': daily_analytics,
            'summary': {
                'total_posts_tracked': len(top_posts),
                'avg_engagement_rate': sum(p['engagement_rate'] for p in top_posts) / len(top_posts) if top_posts else 0,
            }
        }

        logger.info(f"Daily report generated with {len(top_posts)} tracked posts")
        return report

    def export_analytics_csv(self, output_file: str = 'instagram_analytics.csv'):
        """Export analytics to CSV"""
        import csv

        top_posts = self.db.get_top_posts(100)

        with open(output_file, 'w', newline='', encoding='utf-8') as f:
            if not top_posts:
                logger.warning("No analytics to export")
                return

            writer = csv.DictWriter(f, fieldnames=top_posts[0].keys())
            writer.writeheader()
            writer.writerows(top_posts)

        logger.info(f"Analytics exported to {output_file}")


class DailyAutomation:
    """Main orchestrator for daily automation tasks"""

    def __init__(self):
        self.api = InstagramAPI(ACCESS_TOKEN, BUSINESS_ACCOUNT_ID)
        self.db = AnalyticsDatabase()
        self.scheduler = PostScheduler(self.api, self.db)
        self.tracker = AnalyticsTracker(self.api, self.db)

    def run_daily_tasks(self):
        """Run all daily automation tasks"""
        logger.info("Starting daily automation tasks")

        try:
            # 1. Check and publish scheduled posts
            logger.info("Checking for scheduled posts to publish")
            self.scheduler.check_and_publish()

            # 2. Update analytics for recent media
            logger.info("Updating media analytics")
            self.tracker.update_media_analytics()

            # 3. Generate daily report
            logger.info("Generating daily report")
            report = self.tracker.generate_daily_report()

            # 4. Export analytics
            logger.info("Exporting analytics")
            self.tracker.export_analytics_csv()

            logger.info("Daily automation tasks completed successfully")
            return report

        except Exception as e:
            logger.error(f"Error during daily automation: {e}", exc_info=True)
            raise


# Command-line interface
if __name__ == "__main__":
    import sys

    automation = DailyAutomation()

    if len(sys.argv) > 1:
        command = sys.argv[1]

        if command == 'daily':
            # Run daily automation tasks
            automation.run_daily_tasks()

        elif command == 'schedule':
            # Schedule a new post
            if len(sys.argv) < 6:
                print("Usage: python instagram_automation.py schedule <title> <caption> <media_url> <media_type> <scheduled_time>")
                sys.exit(1)

            title = sys.argv[2]
            caption = sys.argv[3]
            media_url = sys.argv[4]
            media_type = sys.argv[5]
            scheduled_time = datetime.fromisoformat(sys.argv[6])
            hashtags = sys.argv[7] if len(sys.argv) > 7 else ''

            post_id = automation.scheduler.schedule_post(title, caption, media_url, media_type, scheduled_time, hashtags)
            print(f"Post scheduled with ID: {post_id}")

        elif command == 'report':
            # Generate report
            report = automation.tracker.generate_daily_report()
            print(json.dumps(report, indent=2, default=str))

        elif command == 'export':
            # Export analytics
            filename = sys.argv[2] if len(sys.argv) > 2 else 'instagram_analytics.csv'
            automation.tracker.export_analytics_csv(filename)
            print(f"Analytics exported to {filename}")

        elif command == 'account':
            # Get account info
            info = automation.api.get_account_info()
            print(json.dumps(info, indent=2))

        else:
            print(f"Unknown command: {command}")
            print("Available commands: daily, schedule, report, export, account")

    else:
        # Default: run daily automation
        automation.run_daily_tasks()
