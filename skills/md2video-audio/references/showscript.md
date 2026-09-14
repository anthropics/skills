````markdown
---
marp: true
theme: gaia
_class: default
paginate: true
allowHtml: true
mermaid: true
style: |
  section {
    /* ===== 全局基准 ===== 
    YAML block scalar（style: |）禁止用 Tab 做缩进
    */
    font-size: 25px;
    line-height: 1.4;
    /* ===== 页面布局 ===== */
    grid-template-columns: 88%; 
    margin: 0 auto;
    padding: 20px;
    display: grid;
    align-content: center;
    justify-content: center; /* 水平居中 */
  }
    /* ===== 代码块 ===== */
  pre {
    font-size: 1em;
    line-height: 1.35;
    margin: 0.5em 0;
    /* 关键：允许内部代码在达到 max-width 时自动换行 */
  	white-space: pre-wrap !important; 
 		word-break: break-word;
  }

  pre code {
    font-size: 1em;
    white-space: pre-wrap !important; /* 允许在长单词、长行内自动换行 */
  	word-break: break-all;
  }

  /* ===== 标题体系 ===== */
  h1 {
    font-size: 1.8em;
    line-height: 1.15;
    margin: 0 0 0.5em;
  }
  h2 {
    font-size: 1.4em;
    line-height: 1.2;
    margin: 0 0 0.4em;
  }
  h3 {
    font-size: 1.2em;
    line-height: 1.25;
    margin: 0 0 0.3em;
  }
  
  /* ===== 正文体系 ===== */
  p {
    margin: 0.5em;
  }
  ul,
  ol {
    margin-top: 0.3em;
    margin-bottom: 0.3em;
  }
  li {
    margin-bottom: 0.25em;
  }
  
  /* ===== 图片 ===== */
  img {
    margin:0.1em auto;
  }
  img[alt="mylogo"] {
    display:block;
    width: 130px ;
    height:130px ;
    border-radius: 50%;
    object-fit: contain;
  }
---

# 核心架构解析

## hi

---

## 章节一：背景介绍

- 向量检索与索引平衡
    - HNSW 索引平衡速度和精度
    - IVF_PQ 算法加速

---

## 章节二：核心代码示例

```python
def hello():
    print("hi")
```
````
