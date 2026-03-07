"""
飞书多维表格同步模块 v1.0

功能：
- 连接飞书多维表格
- 同步持仓数据
- 同步技术信号
- 同步交易记录

数据流向：本地分析结果 → 飞书多维表格（单向同步）

配置说明：
请创建 feishu_config.json 文件，格式参考 feishu_config.example.json
"""

import json
import requests
from typing import Dict, List, Optional, Any, Union
from datetime import datetime
from pathlib import Path
import time
import os


def get_config_path() -> Path:
    """获取配置文件路径"""
    # 优先使用环境变量
    if os.environ.get('FEISHU_CONFIG_PATH'):
        return Path(os.environ['FEISHU_CONFIG_PATH'])

    # 其次使用当前目录
    local_config = Path('./feishu_config.json')
    if local_config.exists():
        return local_config

    # 最后使用用户目录
    home_config = Path.home() / '.stock-master' / 'feishu_config.json'
    if home_config.exists():
        return home_config

    raise FileNotFoundError(
        "找不到飞书配置文件。请创建 feishu_config.json，"
        "或设置环境变量 FEISHU_CONFIG_PATH"
    )


def to_feishu_timestamp(dt: Union[str, datetime, int, None]) -> Optional[int]:
    """
    将日期时间转换为飞书多维表格需要的毫秒时间戳

    参数:
        dt: 日期时间，可以是:
            - datetime 对象
            - 字符串 (格式: 'YYYY-MM-DD' 或 'YYYY-MM-DD HH:MM:SS')
            - 毫秒时间戳 (int)
            - None

    返回:
        毫秒时间戳 或 None
    """
    if dt is None:
        return None

    if isinstance(dt, int):
        # 已经是时间戳，检查是秒还是毫秒
        if dt > 1e12:  # 已经是毫秒
            return dt
        return dt * 1000  # 秒转毫秒

    if isinstance(dt, datetime):
        return int(dt.timestamp() * 1000)

    if isinstance(dt, str):
        # 尝试解析字符串
        formats = [
            '%Y-%m-%d %H:%M:%S',
            '%Y-%m-%d %H:%M',
            '%Y-%m-%d',
            '%Y/%m/%d %H:%M:%S',
            '%Y/%m/%d'
        ]
        for fmt in formats:
            try:
                parsed = datetime.strptime(dt, fmt)
                return int(parsed.timestamp() * 1000)
            except ValueError:
                continue
        # 解析失败，返回当前时间
        return int(time.time() * 1000)

    return int(time.time() * 1000)


class FeishuBitable:
    """飞书多维表格 API 封装"""

    BASE_URL = "https://open.feishu.cn/open-apis"

    def __init__(self, config_path: str = None):
        """
        初始化飞书连接

        参数:
            config_path: 配置文件路径，如不指定则自动查找
        """
        if config_path is None:
            config_path = get_config_path()
        else:
            config_path = Path(config_path)

        if not config_path.exists():
            raise FileNotFoundError(f"配置文件不存在: {config_path}")

        with open(config_path, 'r', encoding='utf-8') as f:
            config = json.load(f)

        self.app_id = config['APP_ID']
        self.app_secret = config['APP_SECRET']
        self.app_token = config['APP_TOKEN']
        self.table_id = config['TABLE_ID']
        self._tenant_access_token = None
        self._token_expires_at = 0

    def _get_tenant_access_token(self) -> str:
        """获取 tenant_access_token"""
        import time

        # 检查 token 是否过期
        if self._tenant_access_token and time.time() < self._token_expires_at - 60:
            return self._tenant_access_token

        url = f"{self.BASE_URL}/auth/v3/tenant_access_token/internal"
        payload = {
            "app_id": self.app_id,
            "app_secret": self.app_secret
        }

        response = requests.post(url, json=payload)
        result = response.json()

        if result.get('code') != 0:
            raise Exception(f"获取 token 失败: {result.get('msg')}")

        self._tenant_access_token = result['tenant_access_token']
        self._token_expires_at = time.time() + result.get('expire', 7200)

        return self._tenant_access_token

    def _request(self, method: str, endpoint: str, data: dict = None) -> dict:
        """发送 API 请求"""
        url = f"{self.BASE_URL}{endpoint}"
        headers = {
            "Authorization": f"Bearer {self._get_tenant_access_token()}",
            "Content-Type": "application/json"
        }

        if method.upper() == 'GET':
            response = requests.get(url, headers=headers, params=data)
        elif method.upper() == 'POST':
            response = requests.post(url, headers=headers, json=data)
        elif method.upper() == 'PUT':
            response = requests.put(url, headers=headers, json=data)
        elif method.upper() == 'DELETE':
            response = requests.delete(url, headers=headers, json=data)
        else:
            raise ValueError(f"不支持的 HTTP 方法: {method}")

        result = response.json()

        if result.get('code') != 0:
            raise Exception(f"API 请求失败: {result.get('msg')}")

        return result.get('data', {})

    # ==========================================
    # 表格操作
    # ==========================================

    def list_tables(self) -> List[dict]:
        """列出多维表格中的所有数据表"""
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables"
        result = self._request('GET', endpoint)
        return result.get('items', [])

    def get_table_fields(self, table_id: str = None) -> List[dict]:
        """获取数据表的字段列表"""
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/fields"
        result = self._request('GET', endpoint)
        return result.get('items', [])

    def create_table(self, name: str, fields: List[dict]) -> dict:
        """
        创建新数据表

        参数:
            name: 表名
            fields: 字段定义列表
        """
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables"
        data = {
            "table": {
                "name": name,
                "default_view_name": "默认视图",
                "fields": fields
            }
        }
        return self._request('POST', endpoint, data)

    # ==========================================
    # 记录操作
    # ==========================================

    def list_records(self, table_id: str = None, page_size: int = 100,
                     filter_str: str = None) -> List[dict]:
        """
        获取数据表记录

        参数:
            table_id: 表 ID
            page_size: 每页数量
            filter_str: 筛选条件
        """
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/records"

        params = {"page_size": page_size}
        if filter_str:
            params["filter"] = filter_str

        result = self._request('GET', endpoint, params)
        return result.get('items', [])

    def create_record(self, fields: dict, table_id: str = None) -> dict:
        """
        创建单条记录

        参数:
            fields: 字段值字典
            table_id: 表 ID
        """
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/records"
        data = {"fields": fields}
        return self._request('POST', endpoint, data)

    def batch_create_records(self, records: List[dict], table_id: str = None) -> dict:
        """
        批量创建记录

        参数:
            records: 记录列表，每条记录为 {"fields": {...}}
            table_id: 表 ID
        """
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/records/batch_create"
        data = {"records": [{"fields": r} if "fields" not in r else r for r in records]}
        return self._request('POST', endpoint, data)

    def update_record(self, record_id: str, fields: dict, table_id: str = None) -> dict:
        """
        更新单条记录

        参数:
            record_id: 记录 ID
            fields: 要更新的字段值
            table_id: 表 ID
        """
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/records/{record_id}"
        data = {"fields": fields}
        return self._request('PUT', endpoint, data)

    def delete_record(self, record_id: str, table_id: str = None) -> dict:
        """删除单条记录"""
        table_id = table_id or self.table_id
        endpoint = f"/bitable/v1/apps/{self.app_token}/tables/{table_id}/records/{record_id}"
        return self._request('DELETE', endpoint)

    def find_record_by_field(self, field_name: str, value: str,
                             table_id: str = None) -> Optional[dict]:
        """
        根据字段值查找记录

        参数:
            field_name: 字段名
            value: 字段值
            table_id: 表 ID

        返回:
            找到的记录或 None
        """
        records = self.list_records(table_id)
        for record in records:
            if record.get('fields', {}).get(field_name) == value:
                return record
        return None


# ==========================================
# Stock Master 同步函数
# ==========================================

def sync_stock_signal(bitable: FeishuBitable, signal_data: dict,
                      table_id: str = None) -> dict:
    """
    同步单只股票的技术信号到飞书

    参数:
        bitable: FeishuBitable 实例
        signal_data: 股票信号数据，格式:
            {
                'ticker': 'AAPL',
                'name': '苹果',
                'current_price': 185.5,
                'score': 5,
                'action': 'BUY',
                'rsi': 45.2,
                'macd_signal': '金叉',
                'kdj_signal': '超卖',
                'patterns': ['锤子线', '双底'],
                'stop_loss': 175.0,
                'take_profit': 200.0,
                'reasons': ['RSI 超卖', 'MACD 金叉'],
                'timestamp': '2026-01-22 15:30:00'
            }
        table_id: 表 ID

    返回:
        创建或更新的记录
    """
    # 转换数据格式为飞书字段格式
    fields = {
        "股票代码": signal_data.get('ticker', ''),
        "股票名称": signal_data.get('name', ''),
        "当前价格": signal_data.get('current_price', 0),
        "综合评分": signal_data.get('score', 0),
        "操作建议": signal_data.get('action', 'HOLD'),
        "RSI": signal_data.get('rsi', 50),
        "MACD信号": signal_data.get('macd_signal', ''),
        "KDJ信号": signal_data.get('kdj_signal', ''),
        "背离信号": signal_data.get('divergence', '无'),
        "形态信号": signal_data.get('patterns', []),  # 多选字段
        "止损价": signal_data.get('stop_loss', 0),
        "止盈价": signal_data.get('take_profit', 0),
        "分析理由": '\n'.join(signal_data.get('reasons', [])),
        "更新时间": to_feishu_timestamp(signal_data.get('timestamp'))
    }

    # 查找是否已存在该股票的记录
    existing = bitable.find_record_by_field("股票代码", fields["股票代码"], table_id)

    if existing:
        # 更新现有记录
        record_id = existing['record_id']
        return bitable.update_record(record_id, fields, table_id)
    else:
        # 创建新记录
        return bitable.create_record(fields, table_id)


def sync_holding(bitable: FeishuBitable, holding_data: dict,
                 table_id: str = None) -> dict:
    """
    同步持仓数据到飞书

    参数:
        holding_data: 持仓数据
    """
    fields = {
        "股票代码": holding_data.get('ticker', ''),
        "股票名称": holding_data.get('name', ''),
        "持仓数量": holding_data.get('quantity', 0),
        "成本价": holding_data.get('cost_price', 0),
        "当前价": holding_data.get('current_price', 0),
        "盈亏金额": holding_data.get('profit_amount', 0),
        "盈亏比例": holding_data.get('profit_ratio', 0),
        "市场": holding_data.get('market', '美股'),
        "买入日期": to_feishu_timestamp(holding_data.get('buy_date')),
        "备注": holding_data.get('note', '')
    }

    existing = bitable.find_record_by_field("股票代码", fields["股票代码"], table_id)

    if existing:
        return bitable.update_record(existing['record_id'], fields, table_id)
    else:
        return bitable.create_record(fields, table_id)


def sync_trade_record(bitable: FeishuBitable, trade_data: dict,
                      table_id: str = None) -> dict:
    """
    同步交易记录到飞书（追加模式）

    参数:
        trade_data: 交易数据
    """
    fields = {
        "股票代码": trade_data.get('ticker', ''),
        "交易类型": trade_data.get('trade_type', '买入'),  # 买入/卖出/做T
        "交易价格": trade_data.get('price', 0),
        "交易数量": trade_data.get('quantity', 0),
        "交易金额": trade_data.get('amount', 0),
        "交易时间": to_feishu_timestamp(trade_data.get('timestamp')),
        "触发信号": trade_data.get('signal', ''),
        "备注": trade_data.get('note', '')
    }

    # 交易记录始终追加，不覆盖
    return bitable.create_record(fields, table_id)


def batch_sync_signals(bitable: FeishuBitable, signals: List[dict],
                       table_id: str = None) -> dict:
    """
    批量同步股票信号

    参数:
        signals: 信号数据列表
    """
    results = {
        'success': 0,
        'failed': 0,
        'errors': []
    }

    for signal in signals:
        try:
            sync_stock_signal(bitable, signal, table_id)
            results['success'] += 1
        except Exception as e:
            results['failed'] += 1
            results['errors'].append({
                'ticker': signal.get('ticker'),
                'error': str(e)
            })

    return results


# ==========================================
# 便捷函数
# ==========================================

def quick_sync_signal(signal_data: dict, config_path: str = None) -> dict:
    """
    快速同步单只股票信号（一行调用）

    示例:
        quick_sync_signal({
            'ticker': 'AAPL',
            'score': 5,
            'action': 'BUY',
            'rsi': 45,
            ...
        })
    """
    bitable = FeishuBitable(config_path)
    return sync_stock_signal(bitable, signal_data)


def test_connection(config_path: str = None) -> dict:
    """
    测试飞书连接

    返回:
        {'status': 'ok', 'tables': [...]} 或错误信息
    """
    try:
        bitable = FeishuBitable(config_path)
        tables = bitable.list_tables()
        return {
            'status': 'ok',
            'message': '连接成功',
            'tables': [{'id': t['table_id'], 'name': t['name']} for t in tables]
        }
    except Exception as e:
        return {
            'status': 'error',
            'message': str(e)
        }


# ==========================================
# 测试
# ==========================================

if __name__ == "__main__":
    print("测试飞书连接...")
    result = test_connection()
    print(json.dumps(result, ensure_ascii=False, indent=2))
