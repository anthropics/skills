#!/usr/bin/env python3
"""
LinkedIn API Integration Example

Demonstrates proper use of LinkedIn's official API with OAuth 2.0 authentication.

IMPORTANT: You must register your application at:
https://www.linkedin.com/developers/apps

Required scopes:
- r_basicprofile
- r_emailaddress
- rw_company_admin (for company data)

This example shows the CORRECT way to integrate with LinkedIn.
DO NOT use automated scrapers or unofficial methods.
"""

from typing import Optional, Dict, Any
import webbrowser
from urllib.parse import urlencode, parse_qs, urlparse


class LinkedInAPI:
    """
    Official LinkedIn API client using OAuth 2.0

    Usage:
        1. Register app at https://www.linkedin.com/developers/apps
        2. Get client_id and client_secret
        3. Set redirect_uri (e.g., http://localhost:8000/callback)
        4. Use this client to authenticate and make API calls
    """

    AUTHORIZATION_URL = 'https://www.linkedin.com/oauth/v2/authorization'
    ACCESS_TOKEN_URL = 'https://www.linkedin.com/oauth/v2/accessToken'
    API_BASE_URL = 'https://api.linkedin.com/v2'

    def __init__(self, client_id: str, client_secret: str, redirect_uri: str):
        """
        Initialize LinkedIn API client

        Args:
            client_id: Your app's client ID from LinkedIn Developer Portal
            client_secret: Your app's client secret
            redirect_uri: OAuth redirect URI (must match app settings)
        """
        self.client_id = client_id
        self.client_secret = client_secret
        self.redirect_uri = redirect_uri
        self.access_token: Optional[str] = None

    def get_authorization_url(self, scope: list[str], state: str = 'random_state') -> str:
        """
        Generate OAuth authorization URL

        Args:
            scope: List of permissions (e.g., ['r_basicprofile', 'r_emailaddress'])
            state: Random string to prevent CSRF attacks

        Returns:
            URL to redirect user for authorization
        """
        params = {
            'response_type': 'code',
            'client_id': self.client_id,
            'redirect_uri': self.redirect_uri,
            'scope': ' '.join(scope),
            'state': state
        }
        return f"{self.AUTHORIZATION_URL}?{urlencode(params)}"

    def exchange_code_for_token(self, code: str) -> Dict[str, Any]:
        """
        Exchange authorization code for access token

        Args:
            code: Authorization code from redirect URL

        Returns:
            Token response with access_token, expires_in, etc.
        """
        import requests

        data = {
            'grant_type': 'authorization_code',
            'code': code,
            'redirect_uri': self.redirect_uri,
            'client_id': self.client_id,
            'client_secret': self.client_secret
        }

        response = requests.post(self.ACCESS_TOKEN_URL, data=data)
        response.raise_for_status()

        token_data = response.json()
        self.access_token = token_data['access_token']
        return token_data

    def get_profile(self) -> Dict[str, Any]:
        """
        Get authenticated user's profile

        Returns:
            User profile data
        """
        import requests

        if not self.access_token:
            raise ValueError("Not authenticated. Call exchange_code_for_token first.")

        headers = {
            'Authorization': f'Bearer {self.access_token}',
            'X-Restli-Protocol-Version': '2.0.0'
        }

        response = requests.get(
            f"{self.API_BASE_URL}/me",
            headers=headers
        )
        response.raise_for_status()
        return response.json()

    def search_companies(self, keywords: str) -> Dict[str, Any]:
        """
        Search for companies (requires appropriate permissions)

        Args:
            keywords: Search keywords

        Returns:
            Company search results
        """
        import requests

        if not self.access_token:
            raise ValueError("Not authenticated. Call exchange_code_for_token first.")

        headers = {
            'Authorization': f'Bearer {self.access_token}',
            'X-Restli-Protocol-Version': '2.0.0'
        }

        params = {
            'q': 'search',
            'keywords': keywords
        }

        response = requests.get(
            f"{self.API_BASE_URL}/companies",
            headers=headers,
            params=params
        )
        response.raise_for_status()
        return response.json()


def example_oauth_flow():
    """
    Example: Complete OAuth 2.0 flow for LinkedIn

    This demonstrates the proper way to authenticate with LinkedIn API.
    """
    import http.server
    import socketserver
    from urllib.parse import parse_qs, urlparse

    # Your app credentials from LinkedIn Developer Portal
    CLIENT_ID = 'your_client_id_here'
    CLIENT_SECRET = 'your_client_secret_here'
    REDIRECT_URI = 'http://localhost:8000/callback'

    # Initialize API client
    api = LinkedInAPI(CLIENT_ID, CLIENT_SECRET, REDIRECT_URI)

    # Step 1: Get authorization URL
    scopes = ['r_basicprofile', 'r_emailaddress']
    auth_url = api.get_authorization_url(scopes, state='random_state_12345')

    print("Step 1: Opening browser for LinkedIn authorization...")
    print(f"Authorization URL: {auth_url}")
    webbrowser.open(auth_url)

    # Step 2: Start local server to receive callback
    print("\nStep 2: Waiting for callback...")

    authorization_code = None

    class CallbackHandler(http.server.SimpleHTTPRequestHandler):
        def do_GET(self):
            nonlocal authorization_code

            # Parse the callback URL
            query = urlparse(self.path).query
            params = parse_qs(query)

            if 'code' in params:
                authorization_code = params['code'][0]
                self.send_response(200)
                self.send_header('Content-type', 'text/html')
                self.end_headers()
                self.wfile.write(b'<html><body><h1>Success!</h1><p>You can close this window.</p></body></html>')
            else:
                self.send_response(400)
                self.end_headers()

        def log_message(self, format, *args):
            pass  # Suppress log messages

    with socketserver.TCPServer(("", 8000), CallbackHandler) as httpd:
        httpd.handle_request()

    if authorization_code:
        print("\nStep 3: Exchanging code for access token...")
        token_data = api.exchange_code_for_token(authorization_code)
        print(f"Access token obtained: {token_data['access_token'][:20]}...")

        # Step 4: Make API call
        print("\nStep 4: Fetching profile...")
        profile = api.get_profile()
        print(f"Profile: {profile}")
    else:
        print("Error: No authorization code received")


def example_sales_navigator_workflow():
    """
    Example: Proper workflow using LinkedIn Sales Navigator

    This is the RECOMMENDED approach for B2B lead generation.
    Requires LinkedIn Sales Navigator license.
    """
    print("""
    RECOMMENDED WORKFLOW: LinkedIn Sales Navigator

    LinkedIn Sales Navigator is the official tool for B2B lead generation:

    1. Purchase Sales Navigator license:
       https://business.linkedin.com/sales-solutions/sales-navigator

    2. Use built-in search features:
       - Advanced search filters (title, company, industry, geography)
       - Lead Builder for targeted list creation
       - Account mapping for org charts

    3. Save leads to lists:
       - Create custom lead lists
       - Tag and organize prospects
       - Set up lead alerts

    4. Export data (within license terms):
       - Use official export functionality
       - Respect daily/monthly limits
       - Export to CRM systems

    5. Integration options:
       - LinkedIn Sales Navigator CRM Sync
       - Official Salesforce integration
       - HubSpot integration

    IMPORTANT: This respects LinkedIn's Terms of Service and provides
    better data quality than any scraping approach.
    """)


def example_manual_research_workflow():
    """
    Example: Manual research workflow (no automation)

    This is the safest, most compliant approach for small-scale research.
    """
    print("""
    MANUAL RESEARCH WORKFLOW

    For ethical, compliant lead research without automation:

    1. Company Website Research:
       - Visit company website
       - Check About Us, Team, Leadership pages
       - Note publicly listed contacts
       - Review Contact Us page for official channels

    2. LinkedIn Manual Search:
       - Use LinkedIn search (not automated)
       - Search for job titles at target company
       - View public profiles only
       - Note profile URLs manually
       - Respect connection request limits

    3. Documentation:
       - Keep notes in CRM system
       - Document source of each contact
       - Track consent and opt-outs
       - Respect privacy preferences

    4. Outreach:
       - Use official company email channels
       - Provide clear opt-out mechanism
       - Respect GDPR/CCPA rights
       - Track consent for communications

    IMPORTANT: This method is slower but 100% compliant with all
    terms of service and privacy regulations.
    """)


if __name__ == '__main__':
    print("LinkedIn API Integration Examples\n")
    print("Choose an example:")
    print("1. OAuth flow with LinkedIn API (proper authentication)")
    print("2. Sales Navigator workflow (recommended for B2B)")
    print("3. Manual research workflow (safest, most compliant)")
    print("\nNote: These are examples showing proper, ethical approaches.")
    print("DO NOT use automated scrapers or unofficial methods.\n")

    # Uncomment the example you want to run:
    # example_oauth_flow()
    # example_sales_navigator_workflow()
    # example_manual_research_workflow()
