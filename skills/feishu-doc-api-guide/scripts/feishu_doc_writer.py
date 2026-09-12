#!/usr/bin/env python3
"""
飞书文档内容添加工具

基于实战验证的飞书 API 使用方法，避免常见陷阱。
"""
import requests
import json
import time
from typing import List, Dict, Any

class FeishuDocWriter:
    """飞书文档写入器"""

    def __init__(self, app_id: str, app_secret: str):
        self.app_id = app_id
        self.app_secret = app_secret
        self.token = None

    def get_token(self) -> str:
        """获取 tenant_access_token"""
        url = "https://open.feishu.cn/open-apis/auth/v3/tenant_access_token/internal"
        response = requests.post(url, json={
            "app_id": self.app_id,
            "app_secret": self.app_secret
        })
        result = response.json()
        if result.get("code") == 0:
            self.token = result["tenant_access_token"]
            return self.token
        raise Exception(f"获取 token 失败: {result}")

    def get_document_info(self, doc_id: str) -> Dict[str, Any]:
        """获取文档信息（包括 revision_id）"""
        if not self.token:
            self.get_token()

        url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}"
        headers = {"Authorization": f"Bearer {self.token}"}
        response = requests.get(url, headers=headers)
        result = response.json()

        if result.get("code") == 0:
            return result["data"]["document"]
        raise Exception(f"获取文档信息失败: {result}")

    def add_blocks(self, doc_id: str, blocks: List[Dict], revision_id: int = None) -> int:
        """
        向文档添加内容块

        关键点：
        1. URL 必须包含 document_revision_id 查询参数
        2. block_type: 2 对应 text 字段（文本块）
        3. block_type: 26 对应 bullet 字段（项目符号列表，但可能不稳定）
        4. 所有 text/bullet 对象必须包含 style: {} 字段

        Args:
            doc_id: 文档 ID
            blocks: 块列表
            revision_id: 文档版本号（如果为 None，会自动获取）

        Returns:
            新的 revision_id
        """
        if not self.token:
            self.get_token()

        if revision_id is None:
            doc_info = self.get_document_info(doc_id)
            revision_id = doc_info["revision_id"]

        # 关键：URL 必须包含 document_revision_id 参数
        url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{doc_id}/children?document_revision_id={revision_id}"

        headers = {
            "Authorization": f"Bearer {self.token}",
            "Content-Type": "application/json"
        }

        data = {"children": blocks}
        response = requests.post(url, headers=headers, json=data)
        result = response.json()

        if result.get("code") == 0:
            return result["data"]["document_revision_id"]
        else:
            raise Exception(f"添加块失败: {result}")

    def create_document(self, title: str) -> str:
        """
        创建新文档

        Returns:
            文档 ID
        """
        if not self.token:
            self.get_token()

        url = "https://open.feishu.cn/open-apis/docx/v1/documents"
        headers = {
            "Authorization": f"Bearer {self.token}",
            "Content-Type": "application/json"
        }

        data = {"title": title}
        response = requests.post(url, headers=headers, json=data)
        result = response.json()

        if result.get("code") == 0:
            return result["data"]["document"]["document_id"]
        raise Exception(f"创建文档失败: {result}")


# 辅助函数：创建常用的块类型

def text_block(content: str, bold: bool = False) -> Dict:
    """创建文本块"""
    return {
        "block_type": 2,
        "text": {
            "elements": [
                {
                    "text_run": {
                        "content": content,
                        **({"text_element_style": {"bold": bold}} if bold else {})
                    }
                }
            ],
            "style": {}
        }
    }

def mixed_text_block(parts: List[tuple]) -> Dict:
    """
    创建混合样式的文本块

    Args:
        parts: [(content, bold), ...] 例如 [("Hello ", False), ("World", True)]
    """
    elements = []
    for content, bold in parts:
        element = {"text_run": {"content": content}}
        if bold:
            element["text_run"]["text_element_style"] = {"bold": True}
        elements.append(element)

    return {
        "block_type": 2,
        "text": {
            "elements": elements,
            "style": {}
        }
    }

def empty_line() -> Dict:
    """创建空行"""
    return text_block("")


# 使用示例
if __name__ == "__main__":
    # 配置（从 ~/.openclaw/openclaw.json 读取）
    import os
    import json

    config_path = os.path.expanduser("~/.openclaw/openclaw.json")
    with open(config_path) as f:
        config = json.load(f)

    feishu_config = config["channels"]["feishu"]

    # 初始化写入器
    writer = FeishuDocWriter(
        app_id=feishu_config["appId"],
        app_secret=feishu_config["appSecret"]
    )

    # 创建新文档
    doc_id = writer.create_document("测试文档")
    print(f"✓ 创建文档: {doc_id}")
    print(f"  链接: https://feishu.cn/docx/{doc_id}")

    # 添加内容
    blocks = [
        text_block("这是标题", bold=True),
        empty_line(),
        text_block("这是普通文本"),
        mixed_text_block([
            ("这是", False),
            ("混合样式", True),
            ("的文本", False)
        ]),
        text_block("• 使用文本块模拟列表项")
    ]

    revision = writer.add_blocks(doc_id, blocks)
    print(f"✓ 添加内容完成，revision: {revision}")
