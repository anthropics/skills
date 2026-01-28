"""
飞书多维表格初始化脚本

功能：创建 Stock Master 所需的表结构
"""

import json
import requests
from feishu_sync import FeishuBitable


def create_field(bitable: FeishuBitable, field_name: str, field_type: int,
                 table_id: str = None, **kwargs) -> dict:
    """
    创建字段

    字段类型:
        1: 文本
        2: 数字
        3: 单选
        4: 多选
        5: 日期
        7: 复选框
    """
    table_id = table_id or bitable.table_id
    endpoint = f"/bitable/v1/apps/{bitable.app_token}/tables/{table_id}/fields"

    data = {
        "field_name": field_name,
        "type": field_type
    }

    # 单选/多选需要配置选项
    if field_type in [3, 4] and 'options' in kwargs:
        data['property'] = {
            'options': [{'name': opt} for opt in kwargs['options']]
        }

    # 数字字段配置
    if field_type == 2 and 'formatter' in kwargs:
        data['property'] = {'formatter': kwargs['formatter']}

    return bitable._request('POST', endpoint, data)


def init_signal_table(bitable: FeishuBitable, table_id: str = None):
    """
    初始化技术信号表字段

    表结构:
    - 股票代码 (文本)
    - 股票名称 (文本)
    - 当前价格 (数字)
    - 综合评分 (数字)
    - 操作建议 (单选: 强烈买入/建议买入/观望/建议卖出/强烈卖出)
    - RSI (数字)
    - MACD信号 (单选: 金叉/多头/空头/死叉)
    - KDJ信号 (单选: 金叉/超卖/中性/超买/死叉)
    - 背离信号 (单选: 无/底背离/顶背离)
    - 形态信号 (多选: 锤子线/吞没/十字星/双底/双顶/头肩/三角形...)
    - 止损价 (数字)
    - 止盈价 (数字)
    - 分析理由 (文本)
    - 更新时间 (日期)
    """
    table_id = table_id or bitable.table_id

    fields_config = [
        ("股票代码", 1, {}),
        ("股票名称", 1, {}),
        ("当前价格", 2, {"formatter": "0.00"}),
        ("综合评分", 2, {"formatter": "0"}),
        ("操作建议", 3, {"options": ["强烈买入", "建议买入", "观望", "建议卖出", "强烈卖出"]}),
        ("RSI", 2, {"formatter": "0.0"}),
        ("MACD信号", 3, {"options": ["金叉", "多头", "空头", "死叉"]}),
        ("KDJ信号", 3, {"options": ["金叉", "超卖", "中性", "超买", "死叉"]}),
        ("背离信号", 3, {"options": ["无", "底背离", "顶背离"]}),
        ("形态信号", 4, {"options": [
            "锤子线", "上吊线", "十字星", "看涨吞没", "看跌吞没",
            "早晨之星", "黄昏之星", "三只白兵", "三只乌鸦",
            "双底", "双顶", "头肩顶", "头肩底",
            "上升三角形", "下降三角形", "对称三角形"
        ]}),
        ("止损价", 2, {"formatter": "0.00"}),
        ("止盈价", 2, {"formatter": "0.00"}),
        ("分析理由", 1, {}),
        ("更新时间", 5, {}),
    ]

    print(f"正在初始化表 {table_id} 的字段...")

    success = 0
    failed = 0

    for field_name, field_type, kwargs in fields_config:
        try:
            create_field(bitable, field_name, field_type, table_id, **kwargs)
            print(f"  ✓ 创建字段: {field_name}")
            success += 1
        except Exception as e:
            if "already exist" in str(e).lower() or "已存在" in str(e):
                print(f"  - 字段已存在: {field_name}")
            else:
                print(f"  ✗ 创建失败: {field_name} - {e}")
                failed += 1

    print(f"\n完成! 成功: {success}, 失败: {failed}")
    return {"success": success, "failed": failed}


def create_holdings_table(bitable: FeishuBitable) -> str:
    """
    创建持仓表

    返回新表的 table_id
    """
    fields = [
        {"field_name": "股票代码", "type": 1},
        {"field_name": "股票名称", "type": 1},
        {"field_name": "市场", "type": 3, "property": {"options": [
            {"name": "美股"}, {"name": "港股"}, {"name": "A股"}
        ]}},
        {"field_name": "持仓数量", "type": 2},
        {"field_name": "成本价", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "当前价", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "市值", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "盈亏金额", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "盈亏比例", "type": 2, "property": {"formatter": "0.00%"}},
        {"field_name": "买入日期", "type": 5},
        {"field_name": "备注", "type": 1},
    ]

    endpoint = f"/bitable/v1/apps/{bitable.app_token}/tables"
    data = {
        "table": {
            "name": "持仓管理",
            "default_view_name": "全部持仓",
            "fields": fields
        }
    }

    result = bitable._request('POST', endpoint, data)
    table_id = result.get('table_id')
    print(f"创建持仓表成功: {table_id}")
    return table_id


def create_trades_table(bitable: FeishuBitable) -> str:
    """
    创建交易记录表

    返回新表的 table_id
    """
    fields = [
        {"field_name": "股票代码", "type": 1},
        {"field_name": "交易类型", "type": 3, "property": {"options": [
            {"name": "买入"}, {"name": "卖出"}, {"name": "做T买"}, {"name": "做T卖"}
        ]}},
        {"field_name": "交易价格", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "交易数量", "type": 2},
        {"field_name": "交易金额", "type": 2, "property": {"formatter": "0.00"}},
        {"field_name": "交易时间", "type": 5},
        {"field_name": "触发信号", "type": 1},
        {"field_name": "备注", "type": 1},
    ]

    endpoint = f"/bitable/v1/apps/{bitable.app_token}/tables"
    data = {
        "table": {
            "name": "交易记录",
            "default_view_name": "全部记录",
            "fields": fields
        }
    }

    result = bitable._request('POST', endpoint, data)
    table_id = result.get('table_id')
    print(f"创建交易记录表成功: {table_id}")
    return table_id


def init_all_tables(config_path: str = None):
    """
    一键初始化所有表结构
    """
    bitable = FeishuBitable(config_path)

    print("=" * 50)
    print("Stock Master 飞书多维表格初始化")
    print("=" * 50)

    # 1. 初始化主表（技术信号表）字段
    print("\n[1/3] 初始化技术信号表...")
    init_signal_table(bitable)

    # 2. 创建持仓表
    print("\n[2/3] 创建持仓管理表...")
    try:
        holdings_table_id = create_holdings_table(bitable)
    except Exception as e:
        if "already exist" in str(e).lower():
            print("  持仓表已存在")
        else:
            print(f"  创建失败: {e}")

    # 3. 创建交易记录表
    print("\n[3/3] 创建交易记录表...")
    try:
        trades_table_id = create_trades_table(bitable)
    except Exception as e:
        if "already exist" in str(e).lower():
            print("  交易记录表已存在")
        else:
            print(f"  创建失败: {e}")

    print("\n" + "=" * 50)
    print("初始化完成！")
    print("=" * 50)

    # 列出所有表
    tables = bitable.list_tables()
    print("\n当前表列表:")
    for t in tables:
        print(f"  - {t['name']} (ID: {t['table_id']})")


if __name__ == "__main__":
    init_all_tables()
