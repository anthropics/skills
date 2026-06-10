import sys
import os

# Add local path for engine import
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from engine import DataEaseChartEngine

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
        print("Please set DATAEASE_ACCESS_KEY, DATAEASE_SECRET_KEY, and DATAEASE_BASE_URL.")
        sys.exit(1)

    if len(sys.argv) < 5:
        print("Usage: python3 deploy.py <type> <title> <dataset_name_or_id> <x_fields> <y_fields>")
        print("Example: python3 deploy.py line 'Skill Test' '电商用户购买行为' '访问平台' '访问次数'")
        sys.exit(1)

    chart_type = sys.argv[1]
    title = sys.argv[2]
    dataset_id = sys.argv[3]
    x_axis = [f.strip() for f in sys.argv[4].split(',') if f.strip()]
    y_axis = [f.strip() for f in sys.argv[5].split(',') if f.strip()]


    engine = DataEaseChartEngine(BASE_URL, ACCESS_KEY, SECRET_KEY)

    try:
        did, url = engine.deploy(chart_type, title, dataset_id, x_axis, y_axis)
        print(f"\n✅ Successfully deployed!")
        print(f"Dashboard ID: {did}")
        print(f"URL: {url}")
    except Exception as e:
        print(f"\n❌ Deployment failed: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()
