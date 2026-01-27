import sys
import json
import subprocess
import re
import urllib.request
import os

def get_repo_info(url):
    """
    Fetches repository information using git ls-remote and direct HTTP requests.
    Returns a dictionary with name, description, latest_hash, and readme content.
    """
    
    # Normalize URL (remove .git suffix if present)
    clean_url = url.rstrip('/')
    if clean_url.endswith('.git'):
        clean_url = clean_url[:-4]
        
    repo_name = clean_url.split('/')[-1]
    
    # 1. Get Latest Commit Hash (using git ls-remote to avoid full clone)
    try:
        # Use git ls-remote to get HEAD
        result = subprocess.run(
            ['git', 'ls-remote', url, 'HEAD'], 
            capture_output=True, 
            text=True, 
            check=True
        )
        # Output format: <hash>\tHEAD
        latest_hash = result.stdout.split()[0]
    except Exception as e:
        print(f"Error fetching git info: {e}", file=sys.stderr)
        latest_hash = "unknown"

    # 2. Fetch README (Try main, then master)
    readme_content = ""
    readme_url_base = clean_url.replace("github.com", "raw.githubusercontent.com")
    
    for branch in ["main", "master"]:
        try:
            readme_url = f"{readme_url_base}/{branch}/README.md"
            with urllib.request.urlopen(readme_url) as response:
                readme_content = response.read().decode('utf-8')
                break
        except Exception:
            continue
            
    if not readme_content:
        # Try lowercase readme
        for branch in ["main", "master"]:
            try:
                readme_url = f"{readme_url_base}/{branch}/readme.md"
                with urllib.request.urlopen(readme_url) as response:
                    readme_content = response.read().decode('utf-8')
                    break
            except Exception:
                continue

    # 3. Construct Result
    return {
        "name": repo_name,
        "url": url,
        "latest_hash": latest_hash,
        "readme": readme_content[:10000] # Truncate if too huge to avoid context blowup
    }

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python fetch_github_info.py <github_url>")
        sys.exit(1)
        
    url = sys.argv[1]
    info = get_repo_info(url)
    print(json.dumps(info, indent=2))
