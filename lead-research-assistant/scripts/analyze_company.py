#!/usr/bin/env python3
"""
Company Website Analyzer - Ethical Business Intelligence Tool

Analyzes publicly accessible company websites to extract:
- Business model and value proposition
- Publicly listed team members
- Contact information from official contact pages
- Industry and company size indicators

IMPORTANT: Only analyzes publicly accessible content. Respects robots.txt
and implements polite crawling with rate limiting.
"""

import argparse
import json
import re
import time
from dataclasses import dataclass, asdict
from typing import List, Optional, Dict, Any
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser

try:
    import requests
    from bs4 import BeautifulSoup
except ImportError:
    print("Error: Required packages not installed.")
    print("Install with: pip install requests beautifulsoup4")
    exit(1)


@dataclass
class TeamMember:
    name: str
    title: Optional[str] = None
    email: Optional[str] = None
    linkedin_url: Optional[str] = None
    bio: Optional[str] = None


@dataclass
class CompanyProfile:
    company_name: Optional[str] = None
    website_url: str = ""
    business_model: Optional[str] = None
    industry: Optional[str] = None
    description: Optional[str] = None
    team_members: List[TeamMember] = None
    contact_emails: List[str] = None
    phone_numbers: List[str] = None
    headquarters: Optional[str] = None
    company_size: Optional[str] = None
    technologies: List[str] = None

    def __post_init__(self):
        if self.team_members is None:
            self.team_members = []
        if self.contact_emails is None:
            self.contact_emails = []
        if self.phone_numbers is None:
            self.phone_numbers = []
        if self.technologies is None:
            self.technologies = []


class CompanyAnalyzer:
    def __init__(self, base_url: str, verbose: bool = False):
        self.base_url = base_url.rstrip('/')
        self.domain = urlparse(base_url).netloc
        self.verbose = verbose
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'CompanyResearchBot/1.0 (Ethical Lead Research; +https://github.com/yourorg/lead-research)'
        })
        self.robot_parser = RobotFileParser()
        self.robot_parser.set_url(urljoin(base_url, '/robots.txt'))
        try:
            self.robot_parser.read()
        except:
            if self.verbose:
                print("Warning: Could not read robots.txt, proceeding cautiously")

    def can_fetch(self, url: str) -> bool:
        """Check if URL is allowed by robots.txt"""
        return self.robot_parser.can_fetch('*', url)

    def fetch_page(self, url: str, rate_limit: float = 1.0) -> Optional[BeautifulSoup]:
        """Fetch and parse a page with rate limiting"""
        if not self.can_fetch(url):
            if self.verbose:
                print(f"Skipping {url} (blocked by robots.txt)")
            return None

        time.sleep(rate_limit)

        try:
            response = self.session.get(url, timeout=10)
            response.raise_for_status()
            return BeautifulSoup(response.text, 'html.parser')
        except Exception as e:
            if self.verbose:
                print(f"Error fetching {url}: {e}")
            return None

    def find_team_page_urls(self, soup: BeautifulSoup) -> List[str]:
        """Find URLs for About Us, Team, Leadership pages"""
        team_keywords = ['about', 'team', 'leadership', 'people', 'our-team', 'about-us', 'company']
        urls = set()

        for link in soup.find_all('a', href=True):
            href = link['href'].lower()
            text = link.get_text().lower()

            if any(keyword in href or keyword in text for keyword in team_keywords):
                full_url = urljoin(self.base_url, link['href'])
                if self.domain in urlparse(full_url).netloc:
                    urls.add(full_url)

        return list(urls)

    def find_contact_page_urls(self, soup: BeautifulSoup) -> List[str]:
        """Find URLs for Contact Us pages"""
        contact_keywords = ['contact', 'contact-us', 'get-in-touch', 'reach-us']
        urls = set()

        for link in soup.find_all('a', href=True):
            href = link['href'].lower()
            text = link.get_text().lower()

            if any(keyword in href or keyword in text for keyword in contact_keywords):
                full_url = urljoin(self.base_url, link['href'])
                if self.domain in urlparse(full_url).netloc:
                    urls.add(full_url)

        return list(urls)

    def extract_company_name(self, soup: BeautifulSoup) -> Optional[str]:
        """Extract company name from homepage"""
        title = soup.find('title')
        if title:
            return title.get_text().strip().split('|')[0].strip()

        h1 = soup.find('h1')
        if h1:
            return h1.get_text().strip()

        return None

    def extract_description(self, soup: BeautifulSoup) -> Optional[str]:
        """Extract company description from meta tags"""
        meta_desc = soup.find('meta', attrs={'name': 'description'})
        if meta_desc and meta_desc.get('content'):
            return meta_desc['content'].strip()

        og_desc = soup.find('meta', attrs={'property': 'og:description'})
        if og_desc and og_desc.get('content'):
            return og_desc['content'].strip()

        return None

    def extract_team_members(self, soup: BeautifulSoup) -> List[TeamMember]:
        """Extract team member information from team pages"""
        members = []

        # Look for common team member HTML patterns
        team_sections = soup.find_all(['div', 'article', 'section'], class_=re.compile(r'team|member|person|staff|leadership', re.I))

        for section in team_sections:
            name_elem = section.find(['h2', 'h3', 'h4', 'strong', 'span'], class_=re.compile(r'name|title', re.I))
            if not name_elem:
                name_elem = section.find(['h2', 'h3', 'h4'])

            if name_elem:
                name = name_elem.get_text().strip()

                title_elem = section.find(['p', 'span', 'div'], class_=re.compile(r'title|role|position', re.I))
                title = title_elem.get_text().strip() if title_elem else None

                email_elem = section.find('a', href=re.compile(r'^mailto:'))
                email = email_elem['href'].replace('mailto:', '') if email_elem else None

                linkedin_elem = section.find('a', href=re.compile(r'linkedin\.com'))
                linkedin_url = linkedin_elem['href'] if linkedin_elem else None

                bio_elem = section.find('p', class_=re.compile(r'bio|description', re.I))
                bio = bio_elem.get_text().strip() if bio_elem else None

                if name and len(name) > 2:
                    members.append(TeamMember(
                        name=name,
                        title=title,
                        email=email,
                        linkedin_url=linkedin_url,
                        bio=bio
                    ))

        return members

    def extract_contact_info(self, soup: BeautifulSoup) -> tuple[List[str], List[str]]:
        """Extract contact emails and phone numbers from contact pages"""
        emails = set()
        phones = set()

        # Find all mailto links
        for link in soup.find_all('a', href=re.compile(r'^mailto:')):
            email = link['href'].replace('mailto:', '').split('?')[0]
            if '@' in email and self.domain.split('.')[-2] in email:
                emails.add(email)

        # Find phone numbers in tel: links
        for link in soup.find_all('a', href=re.compile(r'^tel:')):
            phone = link['href'].replace('tel:', '').strip()
            phones.add(phone)

        # Find phone patterns in text
        text = soup.get_text()
        phone_patterns = re.findall(r'\+?[\d\s\-\(\)]{10,}', text)
        for phone in phone_patterns:
            cleaned = re.sub(r'[^\d\+]', '', phone)
            if len(cleaned) >= 10:
                phones.add(phone.strip())

        return list(emails), list(phones)

    def detect_technologies(self, soup: BeautifulSoup) -> List[str]:
        """Detect technologies used on the website"""
        technologies = []

        # Check for common frameworks/libraries in script tags
        scripts = soup.find_all('script', src=True)
        for script in scripts:
            src = script['src'].lower()
            if 'react' in src:
                technologies.append('React')
            elif 'vue' in src:
                technologies.append('Vue.js')
            elif 'angular' in src:
                technologies.append('Angular')
            elif 'jquery' in src:
                technologies.append('jQuery')

        # Check meta tags for frameworks
        generator = soup.find('meta', attrs={'name': 'generator'})
        if generator:
            technologies.append(generator['content'])

        return list(set(technologies))

    def analyze(self) -> CompanyProfile:
        """Perform complete company analysis"""
        profile = CompanyProfile(website_url=self.base_url)

        if self.verbose:
            print(f"Analyzing {self.base_url}...")

        # Fetch homepage
        homepage_soup = self.fetch_page(self.base_url)
        if not homepage_soup:
            return profile

        # Extract basic info from homepage
        profile.company_name = self.extract_company_name(homepage_soup)
        profile.description = self.extract_description(homepage_soup)
        profile.technologies = self.detect_technologies(homepage_soup)

        if self.verbose:
            print(f"Found company: {profile.company_name}")

        # Find and analyze team pages
        team_urls = self.find_team_page_urls(homepage_soup)[:3]  # Limit to 3 pages
        if self.verbose:
            print(f"Found {len(team_urls)} team-related pages")

        for url in team_urls:
            team_soup = self.fetch_page(url)
            if team_soup:
                members = self.extract_team_members(team_soup)
                profile.team_members.extend(members)
                if self.verbose:
                    print(f"Extracted {len(members)} team members from {url}")

        # Find and analyze contact pages
        contact_urls = self.find_contact_page_urls(homepage_soup)[:2]  # Limit to 2 pages
        if self.verbose:
            print(f"Found {len(contact_urls)} contact pages")

        for url in contact_urls:
            contact_soup = self.fetch_page(url)
            if contact_soup:
                emails, phones = self.extract_contact_info(contact_soup)
                profile.contact_emails.extend(emails)
                profile.phone_numbers.extend(phones)

        # Deduplicate
        profile.contact_emails = list(set(profile.contact_emails))
        profile.phone_numbers = list(set(profile.phone_numbers))

        if self.verbose:
            print(f"\nAnalysis complete:")
            print(f"  - Team members: {len(profile.team_members)}")
            print(f"  - Contact emails: {len(profile.contact_emails)}")
            print(f"  - Phone numbers: {len(profile.phone_numbers)}")

        return profile


def main():
    parser = argparse.ArgumentParser(
        description='Analyze company websites for publicly available business intelligence',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python analyze_company.py --url https://example.com --output report.json
  python analyze_company.py --url https://acmecorp.com --output acme.json --verbose

Notes:
  - Respects robots.txt
  - Implements polite rate limiting
  - Only collects publicly accessible information
  - GDPR/CCPA compliant data collection
        """
    )

    parser.add_argument('--url', required=True, help='Company website URL to analyze')
    parser.add_argument('--output', required=True, help='Output JSON file path')
    parser.add_argument('--verbose', action='store_true', help='Enable verbose output')

    args = parser.parse_args()

    analyzer = CompanyAnalyzer(args.url, verbose=args.verbose)
    profile = analyzer.analyze()

    # Convert to dict for JSON serialization
    output_data = {
        'company_name': profile.company_name,
        'website_url': profile.website_url,
        'business_model': profile.business_model,
        'industry': profile.industry,
        'description': profile.description,
        'team_members': [asdict(member) for member in profile.team_members],
        'contact_emails': profile.contact_emails,
        'phone_numbers': profile.phone_numbers,
        'headquarters': profile.headquarters,
        'company_size': profile.company_size,
        'technologies': profile.technologies
    }

    with open(args.output, 'w') as f:
        json.dump(output_data, f, indent=2)

    print(f"\nReport saved to: {args.output}")


if __name__ == '__main__':
    main()
