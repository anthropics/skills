#!/usr/bin/env python3
"""Multi-source threat intelligence checker. Some features need API keys."""

import sys
import re
import json
import os
import urllib.request
import urllib.parse
import argparse
import threading
from datetime import datetime

# API keys from environment
ABUSEIPDB_KEY = os.getenv("ABUSEIPDB_API_KEY", "")
VT_KEY = os.getenv("VIRUSTOTAL_API_KEY", "")
URLSCAN_KEY = os.getenv("URLSCAN_API_KEY", "")
HIBP_KEY = os.getenv("HIBP_API_KEY", "")


def fetch_json(url, headers=None, method="GET", data=None, timeout=12):
    try:
        req = urllib.request.Request(
            url,
            headers=headers or {"User-Agent": "threat-hunter/1.0", "Accept": "application/json"},
            method=method,
            data=data
        )
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        return {"_error": f"HTTP {e.code}", "_status": e.code}
    except Exception as e:
        return {"_error": str(e)}


def detect_ioc_type(value):
    value = value.strip()
    ipv4_re = re.compile(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$')
    md5_re = re.compile(r'^[a-fA-F0-9]{32}$')
    sha1_re = re.compile(r'^[a-fA-F0-9]{40}$')
    sha256_re = re.compile(r'^[a-fA-F0-9]{64}$')

    if ipv4_re.match(value):
        return "ip"
    if md5_re.match(value) or sha1_re.match(value) or sha256_re.match(value):
        return "hash"
    if "@" in value:
        return "email"
    if value.startswith("http://") or value.startswith("https://"):
        return "url"
    if "." in value and not value.startswith("CVE"):
        return "domain"
    if value.upper().startswith("CVE"):
        return "cve"
    return "unknown"


# --- IP Analysis ---
def check_ip_geoasn(ip):
    url = f"http://ip-api.com/json/{ip}?fields=status,country,countryCode,regionName,city,isp,org,as,asname,proxy,hosting,query"
    return fetch_json(url)


def check_ip_shodan(ip):
    url = f"https://internetdb.shodan.io/{ip}"
    return fetch_json(url, headers={"User-Agent": "threat-hunter/1.0"})


def check_ip_abuseipdb(ip):
    if not ABUSEIPDB_KEY:
        return {"_skipped": "no ABUSEIPDB_API_KEY"}
    url = f"https://api.abuseipdb.com/api/v2/check?ipAddress={ip}&maxAgeInDays=90&verbose=true"
    return fetch_json(url, headers={
        "Key": ABUSEIPDB_KEY,
        "Accept": "application/json",
        "User-Agent": "threat-hunter/1.0"
    })


def check_ip_virustotal(ip):
    if not VT_KEY:
        return {"_skipped": "no VIRUSTOTAL_API_KEY"}
    url = f"https://www.virustotal.com/api/v3/ip_addresses/{ip}"
    return fetch_json(url, headers={"x-apikey": VT_KEY, "User-Agent": "threat-hunter/1.0"})


# --- Domain Analysis ---
def check_domain_virustotal(domain):
    if not VT_KEY:
        return {"_skipped": "no VIRUSTOTAL_API_KEY"}
    url = f"https://www.virustotal.com/api/v3/domains/{domain}"
    return fetch_json(url, headers={"x-apikey": VT_KEY, "User-Agent": "threat-hunter/1.0"})


def check_domain_urlscan(domain):
    url = f"https://urlscan.io/api/v1/search/?q=domain:{domain}&size=5"
    headers = {"User-Agent": "threat-hunter/1.0", "Accept": "application/json"}
    if URLSCAN_KEY:
        headers["API-Key"] = URLSCAN_KEY
    return fetch_json(url, headers=headers)


# --- Hash Analysis ---
def check_hash_virustotal(hash_val):
    if not VT_KEY:
        return {"_skipped": "no VIRUSTOTAL_API_KEY"}
    url = f"https://www.virustotal.com/api/v3/files/{hash_val}"
    return fetch_json(url, headers={"x-apikey": VT_KEY, "User-Agent": "threat-hunter/1.0"})


# --- Email / HIBP ---
def check_email_hibp(email):
    if not HIBP_KEY:
        return {"_skipped": "no HIBP_API_KEY"}
    encoded = urllib.parse.quote(email)
    url = f"https://haveibeenpwned.com/api/v3/breachedaccount/{encoded}"
    return fetch_json(url, headers={
        "hibp-api-key": HIBP_KEY,
        "User-Agent": "threat-hunter/1.0"
    })


# --- CVE Lookup ---
def check_cve(cve_id):
    encoded = urllib.parse.quote(cve_id)
    url = f"https://services.nvd.nist.gov/rest/json/cves/2.0?cveId={encoded}"
    return fetch_json(url, headers={"User-Agent": "threat-hunter/1.0"})


# --- Scoring ---
def score_ip(geo, shodan, abuseipdb, vt):
    score = 0
    reasons = []

    # Shodan tags
    tags = shodan.get("tags", []) if "_error" not in shodan else []
    for tag in tags:
        if tag in ["tor", "vpn", "scanner", "botnet"]:
            score += 25
            reasons.append(f"Shodan tag: {tag}")
        elif tag in ["honeypot"]:
            score += 10

    # Open ports
    ports = shodan.get("ports", []) if "_error" not in shodan else []
    suspicious_ports = [p for p in ports if p in [4444, 1337, 6667, 31337, 9001, 9030]]
    if suspicious_ports:
        score += 15
        reasons.append(f"Suspicious ports: {suspicious_ports}")

    # Shodan vulns
    vulns = shodan.get("vulns", []) if "_error" not in shodan else []
    if vulns:
        score += min(len(vulns) * 5, 20)
        reasons.append(f"Known vulns: {', '.join(vulns[:3])}")

    # AbuseIPDB
    if "_skipped" not in abuseipdb and "_error" not in abuseipdb:
        ab_data = abuseipdb.get("data", {})
        confidence = ab_data.get("abuseConfidenceScore", 0)
        reports = ab_data.get("totalReports", 0)
        if confidence > 50:
            score += 35
            reasons.append(f"AbuseIPDB: {confidence}% confidence, {reports} reports")
        elif confidence > 20:
            score += 15
            reasons.append(f"AbuseIPDB: {confidence}% confidence")

    # VirusTotal
    if "_skipped" not in vt and "_error" not in vt:
        attrs = vt.get("data", {}).get("attributes", {})
        stats = attrs.get("last_analysis_stats", {})
        malicious = stats.get("malicious", 0)
        if malicious > 5:
            score += 30
            reasons.append(f"VirusTotal: {malicious} malicious detections")
        elif malicious > 0:
            score += 10

    # Hosting classification
    if geo.get("hosting"):
        score += 5
        reasons.append("Datacenter/hosting IP")

    return min(score, 100), reasons


def classify_score(score):
    if score >= 70:
        return "MALICIOUS"
    if score >= 40:
        return "SUSPICIOUS"
    if score >= 15:
        return "LOW RISK"
    return "CLEAN"


def print_ip_report(ip, geo, shodan, abuseipdb, vt):
    score, reasons = score_ip(geo, shodan, abuseipdb, vt)
    classification = classify_score(score)
    icons = {"MALICIOUS": "🔴", "SUSPICIOUS": "🟡", "LOW RISK": "🟡", "CLEAN": "🟢"}

    print(f"# Threat Intelligence: {ip}")
    print(f"*{datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}*\n")
    print(f"## Verdict: {icons.get(classification, '⚪')} **{classification}** (Score: {score}/100)\n")

    if geo and "_error" not in geo:
        print("## Geolocation & Infrastructure")
        print(f"- **Location:** {geo.get('city', 'N/A')}, {geo.get('regionName', 'N/A')}, {geo.get('country', 'N/A')}")
        print(f"- **ISP:** {geo.get('isp', 'N/A')}")
        print(f"- **ASN:** {geo.get('as', 'N/A')}")
        if geo.get("proxy"):
            print(f"- **Proxy/VPN:** Yes ⚠️")
        if geo.get("hosting"):
            print(f"- **Hosting/Datacenter:** Yes")
        print()

    if shodan and "_error" not in shodan:
        ports = shodan.get("ports", [])
        tags = shodan.get("tags", [])
        vulns = shodan.get("vulns", [])
        if ports or tags or vulns:
            print("## Shodan Intelligence")
            if ports:
                print(f"- **Open Ports:** {', '.join(map(str, ports))}")
            if tags:
                print(f"- **Tags:** {', '.join(tags)}")
            if vulns:
                print(f"- **Known Vulns:** {', '.join(vulns[:5])}")
            print()

    if "_skipped" not in abuseipdb and "_error" not in abuseipdb:
        ab = abuseipdb.get("data", {})
        print("## AbuseIPDB")
        print(f"- **Confidence Score:** {ab.get('abuseConfidenceScore', 0)}%")
        print(f"- **Total Reports:** {ab.get('totalReports', 0)}")
        print(f"- **Last Reported:** {ab.get('lastReportedAt', 'N/A')}")
        print()
    elif "_skipped" in abuseipdb:
        print(f"*AbuseIPDB: skipped (no API key)*\n")

    if reasons:
        print("## Risk Signals")
        for r in reasons:
            print(f"- ⚠️ {r}")
        print()


def main():
    parser = argparse.ArgumentParser(description="Multi-source threat intelligence")
    parser.add_argument("--ioc", required=True, help="IOC to check (IP, domain, URL, hash, email, CVE)")
    parser.add_argument("--type", help="IOC type (auto-detected if not specified)")
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    args = parser.parse_args()

    ioc = args.ioc.strip()
    ioc_type = args.type or detect_ioc_type(ioc)

    if ioc_type == "ip":
        results = {}
        threads = [
            threading.Thread(target=lambda: results.update({"geo": check_ip_geoasn(ioc)})),
            threading.Thread(target=lambda: results.update({"shodan": check_ip_shodan(ioc)})),
            threading.Thread(target=lambda: results.update({"abuseipdb": check_ip_abuseipdb(ioc)})),
            threading.Thread(target=lambda: results.update({"vt": check_ip_virustotal(ioc)})),
        ]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=15)

        if args.format == "json":
            print(json.dumps(results, indent=2))
        else:
            print_ip_report(ioc, results.get("geo", {}), results.get("shodan", {}),
                          results.get("abuseipdb", {}), results.get("vt", {}))

    elif ioc_type == "domain":
        results = {}
        threads = [
            threading.Thread(target=lambda: results.update({"vt": check_domain_virustotal(ioc)})),
            threading.Thread(target=lambda: results.update({"urlscan": check_domain_urlscan(ioc)})),
        ]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=15)

        if args.format == "json":
            print(json.dumps(results, indent=2))
        else:
            print(f"# Domain Analysis: {ioc}\n")
            if "_skipped" not in results.get("vt", {}) and "_error" not in results.get("vt", {}):
                attrs = results["vt"].get("data", {}).get("attributes", {})
                stats = attrs.get("last_analysis_stats", {})
                print(f"**VirusTotal:** {stats.get('malicious', 0)} malicious / {stats.get('harmless', 0)} clean")
            if results.get("urlscan") and "_error" not in results["urlscan"]:
                total = results["urlscan"].get("total", 0)
                print(f"**urlscan.io:** {total} previous scans found")

    elif ioc_type == "hash":
        data = check_hash_virustotal(ioc)
        if args.format == "json":
            print(json.dumps(data, indent=2))
        else:
            print(f"# File Hash Analysis: {ioc[:16]}...\n")
            if "_skipped" in data:
                print("*VirusTotal: skipped (no API key)*")
            elif "_error" not in data:
                attrs = data.get("data", {}).get("attributes", {})
                stats = attrs.get("last_analysis_stats", {})
                print(f"**Detections:** {stats.get('malicious', 0)}/{sum(stats.values())} engines flagged")
                print(f"**Name:** {attrs.get('meaningful_name', 'Unknown')}")

    elif ioc_type == "email":
        data = check_email_hibp(ioc)
        if args.format == "json":
            print(json.dumps(data, indent=2))
        else:
            print(f"# Email Breach Check: {ioc}\n")
            if "_skipped" in data:
                print("*HIBP: skipped (no API key)*")
            elif "_error" not in data and data.get("_status") != 404:
                print(f"⚠️ **Found in {len(data)} breach(es):**")
                for breach in (data if isinstance(data, list) else []):
                    print(f"- {breach.get('Name', 'Unknown')} ({breach.get('BreachDate', 'N/A')})")
            else:
                print("✅ No breaches found for this email")

    elif ioc_type == "cve":
        data = check_cve(ioc)
        if args.format == "json":
            print(json.dumps(data, indent=2))
        else:
            vulns = data.get("vulnerabilities", [])
            if vulns:
                cve_data = vulns[0].get("cve", {})
                desc = cve_data.get("descriptions", [{}])[0].get("value", "N/A")
                metrics = cve_data.get("metrics", {})
                cvss = metrics.get("cvssMetricV31", [{}])[0].get("cvssData", {}) if metrics.get("cvssMetricV31") else {}
                print(f"# {ioc}\n")
                print(f"**Score:** {cvss.get('baseScore', 'N/A')} ({cvss.get('baseSeverity', 'N/A')})")
                print(f"**Description:** {desc[:400]}")
            else:
                print(f"CVE {ioc} not found in NVD")

    else:
        print(f"Unknown IOC type for: {ioc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
