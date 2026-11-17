import json, re, time, random, os, sys, requests
from typing import List, Dict, Any

# Local SDK client
from client import DataEaseClient
from engine import DataEaseChartEngine

class MultiDataEaseChartEngine(DataEaseChartEngine):
    def __init__(self, base_url, ak, sk):
        super().__init__(base_url, ak, sk)

    def extract_chart_payload(self, chart_type: str, dataset_id: str, x_names: list, y_names: list, view_id: str, layout: dict, title: str = None):
        """
        Reads the single chart template, applies parameters, and extracts the componentData & canvasViewInfo.
        """
        base_dir = os.path.dirname(os.path.abspath(__file__))
        tpl_dir = os.path.join(base_dir, "..", "templates", f"chart_{chart_type}")

        if not os.path.exists(tpl_dir):
            raise FileNotFoundError(f"Template directory {tpl_dir} not found")

        with open(os.path.join(tpl_dir, "template.j2")) as f:
            template_str = f.read()

        with open(os.path.join(tpl_dir, "params.json")) as f:
            raw_params = json.load(f)

        # Build Context (Flatten params + dynamic IDs)
        ctx = {}
        def flatten_dict(d):
            items = {}
            for k, v in d.items():
                if isinstance(v, dict):
                    items.update(flatten_dict(v))
                elif not k.startswith("_"):
                    items[k] = v
            return items

        ctx.update(flatten_dict(raw_params))
        ctx.update(self.get_dataset_ctx(dataset_id, x_names, y_names))

        # Runtime Randomization
        # SCENE_ID is usually "0" for base
        ctx.update({"VIEW_ID": view_id, "SCENE_ID": "0"})

        # Sub placeholder
        def rep(m):
            k = m.group(1).strip()
            if k in ctx:
                return str(ctx[k])
            return m.group(0)

        rendered = re.sub(r"\{\{\s*(\w+)\s*\}\}", rep, template_str)
        payload = json.loads(rendered)

        # Extract canvasViewInfo
        canvas_view_info = payload.get("canvasViewInfo", {})
        target_view_info = canvas_view_info.get(view_id)
        if not target_view_info:
            raise ValueError(f"View ID {view_id} not found in the rendered template!")

        # Override Chart Title in view_info if provided
        if title:
            target_view_info["title"] = title

        # --- Fix: Robust field name replacement ---
        def deep_update_field_names(obj, target_id, new_name):
            if isinstance(obj, dict):
                if str(obj.get("id")) == str(target_id):
                    obj["name"] = new_name
                    if "description" in obj: obj["description"] = new_name
                    if "originName" in obj: obj["originName"] = new_name
                    if "dbFieldName" in obj: obj["dbFieldName"] = None
                    if "optionLabel" in obj:
                        obj["optionLabel"] = new_name + (obj["optionLabel"].partition("(")[1] + obj["optionLabel"].partition("(")[2] if "(" in obj["optionLabel"] else "")
                    if "optionShowName" in obj:
                        obj["optionShowName"] = new_name + (obj["optionShowName"].partition("(")[1] + obj["optionShowName"].partition("(")[2] if "(" in obj["optionShowName"] else "")
                for v in obj.values():
                    deep_update_field_names(v, target_id, new_name)
            elif isinstance(obj, list):
                for item in obj:
                    deep_update_field_names(item, target_id, new_name)

        dataset_ctx = self.get_dataset_ctx(dataset_id, x_names, y_names)
        for i, x_name in enumerate(x_names):
            f_id = dataset_ctx.get(f"XAXIS{'' if i==0 else i+1}_FIELD_ID")
            if f_id: deep_update_field_names(target_view_info, f_id, x_name)

        for i, y_name in enumerate(y_names):
            f_id = dataset_ctx.get(f"YAXIS{'' if i==0 else i+1}_FIELD_ID")
            if f_id: deep_update_field_names(target_view_info, f_id, y_name)

        def brute_force_replace(obj, search_list, replace_list):
            if isinstance(obj, dict):
                for k, v in obj.items():
                    if isinstance(v, str):
                        for s, r in zip(search_list, replace_list):
                            if s in v: obj[k] = v.replace(s, r)
                    else: brute_force_replace(v, search_list, replace_list)
            elif isinstance(obj, list):
                for item in obj: brute_force_replace(item, search_list, replace_list)

        if x_names and y_names:
            brute_force_replace(target_view_info, ["访问平台", "访问次数", "浏览量"], [x_names[0], y_names[0], y_names[0]])
        # --- End Fix ---

        # Extract componentData
        component_data_str = payload.get("componentData", "[]")
        components = json.loads(component_data_str)
        if not components:
            raise ValueError(f"No component data found in the rendered template")

        # We only take the first component as it was a single chart template
        target_component = components[0]

        # Override component name/label if title provided
        if title:
            target_component["name"] = title
            target_component["label"] = title

        # Override layout
        if "layout" in layout:
            layout = layout["layout"] # in case it's nested
            
        if "style" not in target_component:
            target_component["style"] = {}
        
        if "x" in layout: target_component["x"] = layout["x"]
        if "y" in layout: target_component["y"] = layout["y"]
        if "sizeX" in layout: target_component["sizeX"] = layout["sizeX"]
        if "sizeY" in layout: target_component["sizeY"] = layout["sizeY"]
        if "width" in layout: target_component["style"]["width"] = layout["width"]
        if "height" in layout: target_component["style"]["height"] = layout["height"]
        if "left" in layout: target_component["style"]["left"] = layout["left"]
        if "top" in layout: target_component["style"]["top"] = layout["top"]

        return target_component, target_view_info

    def deploy_multi(self, title: str, charts_config: List[Dict[str, Any]]):
        """
        Deploy multiple charts into a single dashboard.
        charts_config supports optional 'layout'. If missing, it will auto-layout.
        """
        content_id = self.rand_id()
        board_name = f"{title}_{int(time.time())}"

        # Load base dashboard style from template
        base_dir = os.path.dirname(os.path.abspath(__file__))
        dashboard_tpl_path = os.path.join(base_dir, "..", "templates", "dashboard", "base.json")
        if os.path.exists(dashboard_tpl_path):
            with open(dashboard_tpl_path) as f:
                base_tpl = json.load(f)
                canvas_style_data = json.loads(base_tpl.get("canvasStyleData", "{}"))
        else:
            canvas_style_data = {
                "width": 1920, "height": 1080, "screenAdaptor": "widthFirst",
                "dashboard": {"gap": "yes", "gapSize": 5, "matrixBase": 4}
            }

        final_component_data = []
        final_canvas_view_info = {}
        active_view_ids = []

        # Auto-layout calculation constants
        GRID_COLS = 72
        CHART_WIDTH = 36
        CHART_HEIGHT = 14

        # Process each chart sequentially
        for idx, c_conf in enumerate(charts_config):
            view_id = self.rand_id()
            active_view_ids.append(view_id)

            # Calculate auto-layout if not provided
            layout = c_conf.get("layout", {})
            if not layout:
                row = idx // 2
                col = idx % 2
                layout = {
                    "x": col * CHART_WIDTH + 1,
                    "y": row * CHART_HEIGHT + 1,
                    "sizeX": CHART_WIDTH,
                    "sizeY": CHART_HEIGHT,
                    "width": 519, "height": 65, # Standard relative sizes
                    "left": col * 519, "top": row * 65
                }

            comp_data, view_info = self.extract_chart_payload(
                chart_type=c_conf["type"],
                dataset_id=c_conf["dataset_name"],
                x_names=c_conf.get("x_axis", []),
                y_names=c_conf.get("y_axis", []),
                view_id=view_id,
                layout=layout,
                title=c_conf.get("title")
            )

            comp_data["_dragId"] = idx
            final_component_data.append(comp_data)
            final_canvas_view_info[view_id] = view_info

        dashboard_payload = {
            "id": None,
            "name": board_name,
            "type": "dashboard",
            "status": 0,
            "dataState": "ready",
            "selfWatermarkStatus": True,
            "checkVersion": "2.10.20",
            "pid": "0",
            "mobileLayout": False,
            "canvasStyleData": json.dumps(canvas_style_data, separators=(',', ':'), ensure_ascii=False),
            "componentData": json.dumps(final_component_data, separators=(',', ':'), ensure_ascii=False),
            "canvasViewInfo": final_canvas_view_info,
            "contentId": content_id
        }

        headers = self.client._get_headers()
        print(f"Deploying multi-chart dashboard '{title}' with {len(charts_config)} charts...")

        save_r = requests.post(
            f"{self.base_url}/dataVisualization/saveCanvas",
            headers=headers, json=dashboard_payload, verify=False, timeout=30
        )

        if save_r.status_code != 200:
            raise Exception(f"saveCanvas failed: {save_r.text}")

        dashboard_id = str(save_r.json()["data"])

        # Publish
        requests.post(
            f"{self.base_url}/dataVisualization/updatePublishStatus",
            headers=headers, verify=False, timeout=30,
            json={
                "id": dashboard_id,
                "name": board_name,
                "activeViewIds": active_view_ids,
                "status": 1,
                "type": "dashboard",
                "mobileLayout": False
            }
        )

        base_preview_url = self.base_url.split('/de2api')[0] if '/de2api' in self.base_url else self.base_url
        return dashboard_id, f"{base_preview_url}/#/preview?dvId={dashboard_id}&dvType=dashboard&ignoreParams=true"

        base_preview_url = self.base_url.split('/de2api')[0] if '/de2api' in self.base_url else self.base_url
        return dashboard_id, f"{base_preview_url}/#/preview?dvId={dashboard_id}&dvType=dashboard&ignoreParams=true"
