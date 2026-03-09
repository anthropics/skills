# 数据采集与清洗

> 原始数据就像刚从矿山开采的矿石——需要经过反复筛选、清洗、提纯，才能变成有价值的训练数据。

## 目录

- [数据采集方法](#数据采集方法)
- [Common Crawl 处理](#common-crawl-处理)
- [数据清洗管线](#数据清洗管线)
- [去重技术](#去重技术)
- [质量过滤](#质量过滤)
- [延伸阅读](#延伸阅读)

---

## 数据采集方法

| 方法 | 规模 | 成本 | 质量 | 适用 |
|------|------|------|------|------|
| **Common Crawl** | PB 级 | 免费 | 低(需清洗) | 预训练 |
| **Web 爬取** | TB 级 | 中 | 中 | 特定领域 |
| **API 采集** | GB-TB | 中高 | 高 | Reddit/StackOverflow |
| **合作采购** | TB 级 | 高 | 高 | 图书/论文 |
| **合成生成** | 无限 | 中 | 中高 | SFT/指令数据 |

---

## Common Crawl 处理

```python
"""Common Crawl 数据处理管线（简化版）"""
import warc
import re
from bs4 import BeautifulSoup
from hashlib import md5

def process_warc_file(warc_path: str):
    """处理单个 WARC 文件"""
    results = []
    
    with warc.open(warc_path) as f:
        for record in f:
            if record['WARC-Type'] != 'response':
                continue
            
            # 1. 提取 HTML
            html = record.payload.read().decode('utf-8', errors='ignore')
            
            # 2. HTML → 纯文本
            soup = BeautifulSoup(html, 'html.parser')
            # 移除脚本、样式等
            for tag in soup.find_all(['script', 'style', 'nav', 'footer']):
                tag.decompose()
            text = soup.get_text(separator='\n', strip=True)
            
            # 3. 基础清洗
            text = clean_text(text)
            
            # 4. 质量过滤
            if quality_check(text):
                results.append({
                    'url': record['WARC-Target-URI'],
                    'text': text,
                    'length': len(text),
                })
    
    return results

def clean_text(text: str) -> str:
    """基础文本清洗"""
    # 统一换行符
    text = text.replace('\r\n', '\n').replace('\r', '\n')
    # 合并多余空行
    text = re.sub(r'\n{3,}', '\n\n', text)
    # 移除多余空格
    text = re.sub(r' {2,}', ' ', text)
    # 移除控制字符
    text = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]', '', text)
    return text.strip()

def quality_check(text: str) -> bool:
    """基础质量检查"""
    # 太短
    if len(text) < 100:
        return False
    # 太多特殊字符
    alpha_ratio = sum(c.isalpha() for c in text) / len(text)
    if alpha_ratio < 0.5:
        return False
    # 重复行过多
    lines = text.split('\n')
    unique_lines = set(lines)
    if len(unique_lines) / max(len(lines), 1) < 0.5:
        return False
    return True
```

---

## 去重技术

### MinHash 去重

```
MinHash — 大规模文本去重的核心算法:

  问题: 100TB 文本数据，找出并删除近似重复的文档
  暴力比对: O(n²)，不可行
  MinHash + LSH: O(n)，可行

  原理:
    1. 文本 → n-gram 集合 (如 5-gram)
    2. 对 n-gram 集合计算多个哈希函数的最小值 → MinHash 签名
    3. MinHash 签名相似 ≈ 原始文档 Jaccard 相似度高
    4. 用 LSH (Locality Sensitive Hashing) 快速找到候选对
    5. 对候选对精确比较

  参数选择:
    n-gram 大小: 5 (平衡精度和召回)
    签名长度: 128-256 (越长越准)
    LSH 桶数: 20 bands × 5 rows
    阈值: Jaccard > 0.8 判定为重复
```

```python
"""MinHash 去重实现（使用 datasketch 库）"""
from datasketch import MinHash, MinHashLSH

def create_minhash(text: str, num_perm: int = 128) -> MinHash:
    """为文本创建 MinHash 签名"""
    m = MinHash(num_perm=num_perm)
    # 5-gram
    words = text.lower().split()
    for i in range(len(words) - 4):
        ngram = ' '.join(words[i:i+5])
        m.update(ngram.encode('utf-8'))
    return m

def deduplicate(documents: list, threshold: float = 0.8) -> list:
    """MinHash LSH 去重"""
    lsh = MinHashLSH(threshold=threshold, num_perm=128)
    
    unique_docs = []
    for i, doc in enumerate(documents):
        mh = create_minhash(doc['text'])
        
        # 查找近似重复
        result = lsh.query(mh)
        if len(result) == 0:
            # 没有重复，保留
            lsh.insert(str(i), mh)
            unique_docs.append(doc)
    
    print(f"原始: {len(documents)}, 去重后: {len(unique_docs)}, "
          f"去除: {len(documents) - len(unique_docs)}")
    return unique_docs
```

### 其他去重方法

| 方法 | 粒度 | 适用场景 | 特点 |
|------|------|---------|------|
| **精确去重** (MD5/SHA) | 文档级 | 完全相同的文档 | 最快但只检测完全重复 |
| **MinHash + LSH** | 文档级 | 近似重复文档 | 标准方法，可扩展 |
| **SimHash** | 文档级 | 近似重复文档 | 单 hash 值，存储高效 |
| **SemDeDup** | 语义级 | 语义重复 | 用嵌入模型判断语义相似 |
| **Suffix Array** | 子串级 | 段落/句子级重复 | 精细去重，计算量大 |

---

## 质量过滤

### 多维度质量评分

```python
"""数据质量评分系统"""

class QualityScorer:
    """多维度文本质量评分"""
    
    def score(self, text: str) -> dict:
        scores = {
            "length": self._length_score(text),
            "language": self._language_score(text),
            "repetition": self._repetition_score(text),
            "coherence": self._coherence_score(text),
            "toxicity": self._toxicity_score(text),
        }
        scores["overall"] = sum(scores.values()) / len(scores)
        return scores
    
    def _length_score(self, text: str) -> float:
        """长度评分: 太短或太长都扣分"""
        length = len(text.split())
        if length < 50: return 0.3
        if length < 200: return 0.7
        if length < 5000: return 1.0
        if length < 50000: return 0.8
        return 0.5  # 超长文档可能有问题
    
    def _language_score(self, text: str) -> float:
        """语言检测: 非目标语言扣分"""
        # 使用 fasttext 或 langdetect
        try:
            from langdetect import detect
            lang = detect(text)
            return 1.0 if lang in ['en', 'zh-cn', 'zh-tw'] else 0.3
        except:
            return 0.5
    
    def _repetition_score(self, text: str) -> float:
        """重复度检测"""
        lines = text.split('\n')
        if not lines:
            return 0.0
        unique = len(set(lines))
        ratio = unique / len(lines)
        return min(ratio * 1.2, 1.0)
    
    def _coherence_score(self, text: str) -> float:
        """连贯性评分 (简化版)"""
        sentences = text.split('.')
        if len(sentences) < 2:
            return 0.5
        # 句子平均长度合理性
        avg_len = sum(len(s.split()) for s in sentences) / len(sentences)
        if 5 < avg_len < 40:
            return 1.0
        return 0.5
    
    def _toxicity_score(self, text: str) -> float:
        """毒性评分 (1.0 = 无毒)"""
        # 实际应使用毒性分类器
        toxic_words = ['hate', 'kill', 'attack']  # 简化
        lower = text.lower()
        count = sum(1 for w in toxic_words if w in lower)
        return max(0, 1.0 - count * 0.2)
```

---

## 延伸阅读

- [CCNet: Extracting High Quality Data from Common Crawl](https://github.com/facebookresearch/cc_net)
- [FineWeb: Curating High Quality Data](https://huggingface.co/spaces/HuggingFaceFW/blogpost-fineweb-v1)
- [datasketch: MinHash LSH](https://ekzhu.com/datasketch/)
- 论文: *Deduplicating Training Data Makes Language Models Better* (Lee et al., 2022)

---

*上一篇：[01-data-lifecycle.md](01-data-lifecycle.md)* | *下一篇：[03-data-labeling.md](03-data-labeling.md)*

*返回：[README.md](README.md) - 章节索引*
