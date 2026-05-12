import os
import json
import sys
import argparse

# Add scripts to path
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from engine import DataEaseChartEngine

def load_dotenv():
    env_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".env")
    if os.path.exists(env_path):
        with open(env_path) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    os.environ[key.strip()] = value.strip().strip('"').strip("'")

def main():
    load_dotenv()
    ak = os.environ.get("DATAEASE_ACCESS_KEY")
    sk = os.environ.get("DATAEASE_SECRET_KEY")
    url = os.environ.get("DATAEASE_BASE_URL")

    if not all([ak, sk, url]):
        print("Error: Missing environment variables DATAEASE_ACCESS_KEY, DATAEASE_SECRET_KEY, or DATAEASE_BASE_URL.")
        sys.exit(1)

    parser = argparse.ArgumentParser(description="Inspect DataEase datasets and fields.")
    parser.add_argument("--list-datasets", action="store_true", help="List all available datasets")
    parser.add_argument("--dataset", type=str, help="Dataset name or ID to inspect fields for")

    args = parser.parse_args()

    engine = DataEaseChartEngine(url, ak, sk)

    if args.list_datasets:
        try:
            headers = engine.client._get_headers()
            import requests
            resp = requests.post(f"{url.rstrip('/')}/datasetTree/tree", headers=headers, json={"busiFlag": "dataset"}, verify=False)
            if resp.status_code == 200:
                nodes = resp.json().get('data', [])
                def list_datasets(items):
                    datasets = []
                    for item in items:
                        if item.get('leaf'):
                            datasets.append((item.get('name'), item.get('id')))
                        children = item.get('children', [])
                        if children:
                            datasets.extend(list_datasets(children))
                    return datasets

                all_ds = list_datasets(nodes)
                print(json.dumps([{"name": n, "id": i} for n, i in all_ds], ensure_ascii=False, indent=2))
            else:
                print(f"Error fetching datasets: {resp.text}")
        except Exception as e:
            print(f"Error: {e}")

    elif args.dataset:
        try:
            ds_id = engine.resolve_dataset_id(args.dataset)
            # Try getting details first
            import requests
            headers = engine.client._get_headers()
            url_detail = f"{url.rstrip('/')}/datasetTree/details/{ds_id}"
            resp = requests.get(url_detail, headers=headers, verify=False)
            fields = []
            if resp.status_code == 200:
                fields = resp.json().get('data', {}).get('allFields', [])

            if not fields:
                resp = engine.client.post(f"/datasetField/listByDatasetGroup/{ds_id}")
                fields = resp.json().get('data', [])

            print(json.dumps([{"name": f['name'], "id": f['id'], "type": f.get('deType'), "dataeaseName": f.get('dataeaseName')} for f in fields], ensure_ascii=False, indent=2))
        except Exception as e:
            print(f"Error: {e}")
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
