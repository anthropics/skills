import ast
import json
import re
from typing import Optional, Any
from loguru import logger

def _strip_comments(text: str) -> str:
    """
    Safely remove C-style comments (// and /* */) from JSON-like text,
    preserving strings (including URLs like http://).
    """
    result = []
    i = 0
    n = len(text)
    in_string = False
    escape = False
    
    while i < n:
        char = text[i]
        
        if in_string:
            if char == '\\':
                escape = not escape
            elif char == '"' and not escape:
                in_string = False
            else:
                escape = False
            result.append(char)
            i += 1
            continue
            
        # Not in string
        if char == '"':
            in_string = True
            result.append(char)
            i += 1
            continue
            
        # Check for // comment
        if i + 1 < n and text[i:i+2] == '//':
            i += 2
            while i < n and text[i] != '\n':
                i += 1
            continue
            
        # Check for /* comment
        if i + 1 < n and text[i:i+2] == '/*':
            i += 2
            while i + 1 < n and text[i:i+2] != '*/':
                i += 1
            i += 2
            continue
            
        result.append(char)
        i += 1
        
    return ''.join(result)

def extract_json(text: str) -> Optional[Any]:
    """
    更加鲁棒的 JSON 提取工具。
    处理:
    1. Markdown 代码块 (```json ... ```)
    2. 首尾多余字符
    3. 同一个文本中多个 JSON 对象 (仅提取第一个)
    4. 简单的 JSON 修复 (末尾逗号等)
    5. C 风格注释 (// 和 /* */)
    """
    if not text:
        return None
    
    # 1. 清理明显的 Markdown 包装
    text = text.strip()
    
    # 先尝试精确匹配 ```json ... ``` 或 ```...```
    md_match = re.search(r'```(?:json)?\s*\n?(.*?)\n?```', text, re.DOTALL)
    if md_match:
        text = md_match.group(1).strip()
    elif text.startswith("```"):
        # 回退：如果开头有 ``` 但没完整匹配
        text = re.sub(r'^```[a-z]*\n?', '', text)
        text = re.sub(r'\n?```\s*$', '', text)
    
    # 2. 寻找第一个 JSON 起始符 { 或 [
    start_brace = text.find('{')
    start_bracket = text.find('[')
    
    if start_brace == -1 and start_bracket == -1:
        return None
        
    start_idx = start_brace if (start_bracket == -1 or (start_brace != -1 and start_brace < start_bracket)) else start_bracket
    
    # 2.5 预处理：修复一些极其常见的 LLM 错误
    potential_json = text[start_idx:].strip()
    
    # remove comments safely
    potential_json = _strip_comments(potential_json)
    
    # b. 修复缺失开头引号的键:  nodes": [  -> "nodes": [
    # 匹配模式: (空白或换行) 单词 紧跟引号和冒号
    potential_json = re.sub(r'([\{\,]\s*)([a-zA-Z_]\w*)\"\s*:', r'\1"\2":', potential_json)
    
    # c. 修复缺失末尾引号的键:  "nodes: [ -> "nodes": [
    potential_json = re.sub(r'([\{\,]\s*)\"([a-zA-Z_]\w*)\s*:', r'\1"\2":', potential_json)

    # d. 修复完全缺失引号的键: nodes: [ -> "nodes": [
    # 注意避免匹配到像 http:// 这种内容，所以限定在 { 或 , 之后
    potential_json = re.sub(r'([\{\,]\s*)([a-zA-Z_]\w*)\s*:', r'\1"\2":', potential_json)
    
    # 3. 使用 raw_decode 尝试解析
    decoder = json.JSONDecoder()
    
    # 首先尝试直接解析（不做任何预处理）
    try:
        obj = json.loads(potential_json)
        return obj
    except json.JSONDecodeError:
        pass
    
    # 简单预处理：移除对象/列表末位多余逗号
    processed_json = re.sub(r',\s*([\]}])', r'\1', potential_json)
    
    try:
        obj, end_pos = decoder.raw_decode(processed_json)
        return obj
    except json.JSONDecodeError:
        pass
    
    # e. 修复未终止的字符串字面量问题：移除值中的实际换行符
    # LLM 可能在字符串值中生成包含真实 newline 的内容，导致 JSON 非法
    def fix_multiline_strings(s):
        # 简单策略：将字符串值内的换行替换为空格
        lines = s.split('\n')
        result = []
        in_string = False
        for line in lines:
            # 计算未转义的引号数
            quote_count = line.count('"') - line.count('\\"')
            if in_string:
                result[-1] += ' ' + line.strip()
            else:
                result.append(line)
            
            if quote_count % 2 == 1:
                in_string = not in_string
        return '\n'.join(result)
    
    fixed_json = fix_multiline_strings(processed_json)
    
    try:
        obj, end_pos = decoder.raw_decode(fixed_json)
        return obj
    except json.JSONDecodeError:
        try:
            # 4. 尝试处理单引号问题 (JSON 规范要求双引号，但 LLM 常输出单引号)
            # 这是一个简单的替换技巧，仅针对像 {'key': 'value'} 这样的结构
            # 注意：这可能会破坏包含单引号的字符串值，所以作为较后的回退
            fix_quotes = re.sub(r"'(.*?)':", r'"\1":', processed_json) # 修复键
            fix_quotes = re.sub(r":\s*'(.*?)'", r': "\1"', fix_quotes)   # 修复简单值
            obj, end_pos = decoder.raw_decode(fix_quotes)
            return obj
        except (json.JSONDecodeError, TypeError):
            try:
                # 5. 使用 ast.literal_eval 作为终极回退 (处理 Python 字典格式)
                # 提取第一个匹配的括号对内容
                # 寻找匹配的 { }
                stack = []
                for i, char in enumerate(potential_json):
                    if char == '{': stack.append('{')
                    elif char == '}':
                        if stack: stack.pop()
                        if not stack:
                            content = potential_json[:i+1]
                            return ast.literal_eval(content)
            except (ValueError, SyntaxError, MemoryError) as e:
                logger.warning(f"All JSON extraction attempts failed: {e}")
            except Exception as e:
                logger.error(f"Unexpected error during JSON extraction: {e}")
    
    return None
