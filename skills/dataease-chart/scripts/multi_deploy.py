import sys
import os
import json

# Add local path for engine import
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from multi_engine import MultiDataEaseChartEngine

# --- Configuration from Environment ---
def load_dotenv():
    env_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".env")
    if os.path.exists(env_path):
        with open(env_path) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    os.environ[key.strip()] = value.strip().strip('"').strip("'")

load_dotenv()

ACCESS_KEY = os.environ.get("DATAEASE_ACCESS_KEY")
SECRET_KEY = os.environ.get("DATAEASE_SECRET_KEY")
BASE_URL   = os.environ.get("DATAEASE_BASE_URL")

def main():
    if not all([ACCESS_KEY, SECRET_KEY, BASE_URL]):
        print("Error: Missing required environment variables.")
        sys.exit(1)

    if len(sys.argv) < 3:
        print("Usage: python3 multi_deploy.py <dashboard_title> <charts_json_config>")
        print("Example: python3 multi_deploy.py '综合分析' '[{\"type\":\"bar\",\"dataset_name\":\"ds1\",\"x_axis\":[\"f1\"],\"y_axis\":[\"f2\"]}]'")
        sys.exit(1)

    title = sys.argv[1]
    try:
        charts_config = json.loads(sys.argv[2])
    except Exception as e:
        print(f"Error parsing JSON config: {e}")
        sys.exit(1)

    engine = MultiDataEaseChartEngine(BASE_URL, ACCESS_KEY, SECRET_KEY)

    try:
        did, url = engine.deploy_multi(title, charts_config)
        print(f"\n✅ Successfully deployed multi-chart dashboard!")
        print(f"Dashboard ID: {did}")
        print(f"URL: {url}")
    except Exception as e:
        print(f"\n❌ Deployment failed: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()
