import os
from typing import Dict, List, Any, Optional
import pandas as pd
from loguru import logger
from pyecharts.charts import Kline, Line, Bar, Grid, Radar, Graph
from pyecharts import options as opts
from pyecharts.globals import ThemeType
from datetime import datetime, timedelta

class VisualizerTools:
    """可视化工具库 - 使用 Pyecharts 生成 HTML 图表"""

    @staticmethod
    def generate_stock_chart(
        df: pd.DataFrame, 
        ticker: str, 
        title: str = None,
        prediction: Optional[List[float]] = None,
        forecast: Optional[Any] = None, # ForecastResult instance
        ground_truth: Optional[pd.DataFrame] = None # For training visualization
    ) -> Grid:
        """
        生成股票 K 线图 + 成交量 + 预测趋势 (支持多状态 K 线)
        """
        if df.empty:
            return None

        # 数据预处理
        df = df.sort_values('date')
        dates = [str(d)[:10] for d in df['date'].tolist()]
        k_data = df[['open', 'close', 'low', 'high']].values.tolist()
        volumes = df['volume'].tolist()
        
        if not title:
            title = f"{ticker} 股价走势与预测"
            
        legend_items = ["日K"]
        
        # 1. 处理传统的简单预测线 (Line)
        pred_line = None
        if prediction and not forecast:
            try:
                last_date_str = dates[-1]
                last_date = datetime.strptime(last_date_str, "%Y-%m-%d")
                
                pred_dates = []
                for i in range(1, len(prediction) + 1):
                    pred_dates.append((last_date + timedelta(days=i)).strftime("%Y-%m-%d"))
                
                ext_dates = dates + pred_dates
                last_close = df.iloc[-1]['close']
                pred_values = [None] * (len(df) - 1) + [float(last_close)] + prediction
                
                pred_line = (
                    Line()
                    .add_xaxis(ext_dates)
                    .add_yaxis(
                        "AI预测趋势",
                        pred_values,
                        is_connect_nones=True,
                        is_symbol_show=True,
                        linestyle_opts=opts.LineStyleOpts(width=2, type_="dashed", color="#FF8C00"),
                        label_opts=opts.LabelOpts(is_show=False)
                    )
                )
                dates = ext_dates
                legend_items.append("AI预测趋势")
            except Exception as e:
                logger.error(f"Failed to process simple prediction: {e}")

        # 2. 处理复杂的 Kronos 预测 (Kline)
        base_kline = None
        adj_kline = None
        
        if forecast:
            try:
                # 获取预测数据点
                base_points = forecast.base_forecast # List[KLinePoint]
                adj_points = forecast.adjusted_forecast # List[KLinePoint]
                
                # 提取日期
                pred_dates = [str(p.date)[:10] for p in (adj_points or base_points)]
                
                # 检查日期是否已经包含在主 dates 中，如果没有则扩展
                if pred_dates and pred_dates[0] not in dates:
                    dates = dates + pred_dates
                
                # 构建 Baseline 预测 K 线数据
                if base_points:
                    # 前面填充 None
                    base_k_data = [[None]*4] * len(df) + [[p.open, p.close, p.low, p.high] for p in base_points]
                    base_kline = (
                        Kline()
                        .add_xaxis(dates)
                        .add_yaxis(
                            "模型原始预测",
                            base_k_data,
                            itemstyle_opts=opts.ItemStyleOpts(
                                color="transparent",
                                color0="transparent",
                                border_color="#FF8C00", # 橙色
                                border_color0="#FF8C00",
                                opacity=0.6,
                                border_type="dashed"
                            ),
                        )
                    )
                    legend_items.append("模型原始预测")

                # 构建 Adjusted 调优 K 线数据
                if adj_points:
                    adj_k_data = [[None]*4] * len(df) + [[p.open, p.close, p.low, p.high] for p in adj_points]
                    adj_kline = (
                        Kline()
                        .add_xaxis(dates)
                        .add_yaxis(
                            "LLM调优预测",
                            adj_k_data,
                            itemstyle_opts=opts.ItemStyleOpts(
                                color="#9333ea", # 紫色
                                color0="#9333ea",
                                border_color="#9333ea",
                                border_color0="#9333ea",
                                opacity=0.8
                            ),
                        )
                    )
                    legend_items.append("LLM调优预测")
                    
            except Exception as e:
                logger.error(f"Failed to process complex forecast: {e}")

        # 2.5 处理 Ground Truth (用于训练评估可视化)
        gt_line = None
        if ground_truth is not None and not ground_truth.empty:
            try:
                gt_dates = [str(d)[:10] for d in ground_truth['date'].tolist()]
                # 确保日期包含在 dates 中
                for d in gt_dates:
                    if d not in dates:
                        dates.append(d)
                dates = sorted(list(set(dates))) # Re-sort to maintain order

                gt_values = [None] * len(dates)
                for _, row in ground_truth.iterrows():
                    d_str = str(row['date'])[:10]
                    if d_str in dates:
                        idx = dates.index(d_str)
                        gt_values[idx] = float(row['close'])

                gt_line = (
                    Line()
                    .add_xaxis(dates)
                    .add_yaxis(
                        "真实走势 (GT)",
                        gt_values,
                        is_connect_nones=True,
                        linestyle_opts=opts.LineStyleOpts(width=3, color="#2ecc71"), # 绿色粗线
                        label_opts=opts.LabelOpts(is_show=False)
                    )
                )
                legend_items.append("真实走势 (GT)")
            except Exception as e:
                logger.error(f"Failed to process ground truth: {e}")

        # 3. 主 K 线图
        # 为了展示预测，也需要对主 K 线数据进行填充
        main_k_data = k_data + [[None]*4] * (len(dates) - len(df))
        
        kline = (
            Kline()
            .add_xaxis(dates)
            .add_yaxis(
                "日K",
                main_k_data,
                itemstyle_opts=opts.ItemStyleOpts(
                    color="#ef4444",  # 跌
                    color0="#22c55e", # 涨
                    border_color="#ef4444",
                    border_color0="#22c55e",
                ),
            )
            .set_global_opts(
                title_opts=opts.TitleOpts(title=title, pos_left="center"),
                xaxis_opts=opts.AxisOpts(is_scale=True),
                yaxis_opts=opts.AxisOpts(
                    is_scale=True,
                    splitarea_opts=opts.SplitAreaOpts(
                        is_show=True, areastyle_opts=opts.AreaStyleOpts(opacity=1)
                    ),
                ),
                legend_opts=opts.LegendOpts(is_show=True, pos_top="5%"),
                datazoom_opts=[opts.DataZoomOpts(type_="inside", range_start=50)],
                tooltip_opts=opts.TooltipOpts(trigger="axis", axis_pointer_type="cross"),
            )
        )
        
        # Overlap all series
        if pred_line: kline.overlap(pred_line)
        if base_kline: kline.overlap(base_kline)
        if adj_kline: kline.overlap(adj_kline)
        if gt_line: kline.overlap(gt_line)

        # 4. 成交量柱状图
        # 同理扩展成交量数据
        ext_volumes = volumes + [0] * (len(dates) - len(df))
        
        bar = (
            Bar()
            .add_xaxis(dates)
            .add_yaxis(
                "成交量",
                ext_volumes,
                xaxis_index=1,
                yaxis_index=1,
                label_opts=opts.LabelOpts(is_show=False),
                itemstyle_opts=opts.ItemStyleOpts(color="#7fbe9e"),
            )
            .set_global_opts(
                xaxis_opts=opts.AxisOpts(
                    type_="category",
                    grid_index=1,
                    axislabel_opts=opts.LabelOpts(is_show=False),
                ),
                legend_opts=opts.LegendOpts(is_show=False),
            )
        )

        # 5. 组合 Grid
        grid_chart = Grid(init_opts=opts.InitOpts(width="100%", height="450px", theme=ThemeType.LIGHT))
        grid_chart.add(
            kline,
            grid_opts=opts.GridOpts(pos_left="10%", pos_right="8%", height="50%"),
        )
        grid_chart.add(
            bar,
            grid_opts=opts.GridOpts(
                pos_left="10%", pos_right="8%", pos_top="65%", height="20%"
            ),
        )

        return grid_chart

    @staticmethod
    def generate_loss_chart(losses: List[float], title: str = "训练损失收敛曲线") -> Line:
        """生成 Loss 下降曲线图"""
        line = (
            Line(init_opts=opts.InitOpts(width="100%", height="400px", theme=ThemeType.LIGHT))
            .add_xaxis(list(range(1, len(losses) + 1)))
            .add_yaxis(
                "Training Loss",
                losses,
                is_smooth=True,
                linestyle_opts=opts.LineStyleOpts(width=2, color="#3b82f6"),
                label_opts=opts.LabelOpts(is_show=False),
                markpoint_opts=opts.MarkPointOpts(data=[opts.MarkPointItem(type_="min", name="最小值")])
            )
            .set_global_opts(
                title_opts=opts.TitleOpts(title=title, pos_left="center"),
                xaxis_opts=opts.AxisOpts(name="Epoch", is_scale=True),
                yaxis_opts=opts.AxisOpts(name="Loss", is_scale=True),
                tooltip_opts=opts.TooltipOpts(trigger="axis"),
            )
        )
        return line

    @staticmethod
    def generate_sentiment_trend_chart(sentiment_history: List[Dict[str, Any]]) -> Line:
        """
        生成舆情情绪趋势图
        :param sentiment_history: [{"date": "2024-01-01", "score": 0.8}, ...]
        """
        dates = [item['date'] for item in sentiment_history]
        scores = [item['score'] for item in sentiment_history]

        line = (
            Line(init_opts=opts.InitOpts(width="100%", height="300px", theme=ThemeType.LIGHT))
            .add_xaxis(dates)
            .add_yaxis(
                "情绪指数",
                scores,
                is_smooth=True,
                markline_opts=opts.MarkLineOpts(data=[opts.MarkLineItem(y=0, name="中性线")]),
                itemstyle_opts=opts.ItemStyleOpts(color="#5470c6"),
                areastyle_opts=opts.AreaStyleOpts(opacity=0.3, color="#5470c6")
            )
            .set_global_opts(
                title_opts=opts.TitleOpts(title="舆情情绪趋势", pos_left="center"),
                legend_opts=opts.LegendOpts(pos_top="8%"),
                yaxis_opts=opts.AxisOpts(min_=-1, max_=1, name="Sentiment"),
                tooltip_opts=opts.TooltipOpts(trigger="axis"),
            )
        )
        return line

    @staticmethod
    def generate_isq_radar_chart(sentiment: float, confidence: float, intensity: int, 
                               expectation_gap: float = 0.5, timeliness: float = 0.8,
                               title: str = "信号质量 ISQ 评估") -> Radar:
        """生成信号质量雷达图"""
        # 标准化数据 (0-100)
        # sentiment 强度: 绝对值越大强度越高
        sent_val = min(100, abs(sentiment) * 100)
        # confidence: 0 to 1 -> 0 to 100
        conf_val = confidence * 100
        # intensity: 1 to 5 -> 20 to 100
        int_val = intensity * 20
        # gap & time: 0 to 1 -> 0 to 100
        gap_val = expectation_gap * 100
        time_val = timeliness * 100

        schema = [
            opts.RadarIndicatorItem(name="情绪强度", max_=100),
            opts.RadarIndicatorItem(name="确定性", max_=100),
            opts.RadarIndicatorItem(name="影响力", max_=100),
            opts.RadarIndicatorItem(name="预期差", max_=100),
            opts.RadarIndicatorItem(name="时效性", max_=100),
        ]

        radar = (
            Radar(init_opts=opts.InitOpts(width="100%", height="400px", theme=ThemeType.LIGHT))
            .add_schema(schema=schema)
            .add(
                "信号特征",
                [[sent_val, conf_val, int_val, gap_val, time_val]],
                color="#f97316",
                areastyle_opts=opts.AreaStyleOpts(opacity=0.3, color="#fb923c"),
            )
            .set_global_opts(
                title_opts=opts.TitleOpts(title=title, pos_left="center"),
                legend_opts=opts.LegendOpts(is_show=False),
            )
        )
        return radar

    @staticmethod
    def generate_transmission_graph(nodes_data: List[Dict[str, str]], title: str = "投资逻辑传导链条") -> Graph:
        """生成逻辑传导拓扑图 (支持分支结构)"""
        nodes = []
        links = []
        
        # Helper for text wrapping
        def wrap_text(text, width=6):
            return '\n'.join([text[i:i+width] for i in range(0, len(text), width)])

        # Map original names to wrapped names to handle links
        name_map = {} 

        for i, item in enumerate(nodes_data):
            # 节点样式
            color = "#ef4444" if "利空" in item.get("impact_type", "") else "#22c55e"
            if "中性" in item.get("impact_type", ""): color = "#6b7280"
            
            original_name = item.get("node_name", f"节点{i}")
            wrapped_name = wrap_text(original_name)
            name_map[original_name] = wrapped_name
            name_map[str(item.get("id", ""))] = wrapped_name # Map ID if present

            nodes.append({
                "name": wrapped_name,
                "symbolSize": 60 if i == 0 else 50,
                "value": item.get("logic", ""),
                "itemStyle": {"color": color},
                # Improve label readability
                "label": {"show": True, "formatter": "{b}"} 
            })
            
            # Logic for Links
            source_key = item.get("source") or item.get("parent") or item.get("parent_id")
            if source_key:
                # Branching logic: Link from specified source
                # Source needs to be resolved to its (wrapped) name
                target_source_name = name_map.get(source_key)
                if not target_source_name and source_key in name_map.values():
                     target_source_name = source_key # It was already a mapped name?
                
                # If we found the source in our map (meaning it appeared before this node)
                if target_source_name:
                    links.append({"source": target_source_name, "target": wrapped_name})
            elif i > 0:
                # Fallback: Linear chain
                links.append({"source": nodes[i-1]["name"], "target": wrapped_name})

        graph = (
            Graph(init_opts=opts.InitOpts(width="100%", height="400px", theme=ThemeType.LIGHT))
            .add(
                "",
                nodes,
                links,
                repulsion=5000,
                layout="force",
                is_roam=True,
                is_draggable=True,
                symbol="circle",
                edge_symbol=['circle', 'arrow'], # Add arrows
                edge_symbol_size=[4, 10],
                linestyle_opts=opts.LineStyleOpts(width=2, curve=0.2, opacity=0.9),
                label_opts=opts.LabelOpts(is_show=True, position="inside", color="white", font_size=10),
                edge_label=opts.LabelOpts(is_show=False),
            )
            .set_global_opts(
                title_opts=opts.TitleOpts(title=title, pos_left="center"),
                tooltip_opts=opts.TooltipOpts(formatter="{b}: {c}")
            )
        )
        return graph

    @staticmethod
    def render_drawio_to_html(xml_content: str, filename: str, title: str = "Logic Diagram") -> str:
        """
        将 Draw.io XML 渲染为包含 Viewer 的 HTML 文件
        """
        import json
        
        # 构造配置字典
        config = {
            "highlight": "#0000ff",
            "nav": True,
            "resize": True,
            "toolbar": "zoom",
            "xml": xml_content
        }
        
        # 1. 转为 JSON 字符串 (自动处理内部的引号转义、换行符转义等)
        json_str = json.dumps(config)
        
        # 2. 转为 HTML 属性安全的字符串 (主要是转义单引号，因为我们在 HTML 中用单引号包裹)
        import html
        safe_json_str = html.escape(json_str, quote=True)
        
        html_template = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="UTF-8">
            <title>{title}</title>
            <style>
                body {{ font-family: sans-serif; padding: 20px; }}
                .mxgraph {{ border: 1px solid #ddd; background: #fff; }}
            </style>
        </head>
        <body>
            <h2>{title}</h2>
            <div class="mxgraph" style="max-width:100%;border:1px solid transparent;" data-mxgraph='{safe_json_str}'></div>
            <script type="text/javascript" src="https://viewer.diagrams.net/js/viewer-static.min.js"></script>
        </body>
        </html>
        """
        
        try:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            # Use 'w' mode with utf-8 encoding
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(html_template)
            logger.info(f"✅ Draw.io chart rendered to {filename}")
            return filename
        except Exception as e:
            logger.error(f"Failed to render drawio chart: {e}")
            return ""

    @staticmethod
    def render_chart_to_file(chart: Any, filename: str) -> str:
        """渲染并保存 HTML"""
        try:
            # 确保目录存在
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            chart.render(filename)
            logger.info(f"✅ Chart rendered to {filename}")
            return filename
        except Exception as e:
            logger.error(f"Failed to render chart: {e}")
            return ""
