# NCBI Database Skill - 中文使用教程

> 一个强大的命令行工具，用于查询 NCBI（美国国家生物技术信息中心）数据库

## 目录

1. [安装](#安装)
2. [快速开始](#快速开始)
3. [命令详解](#命令详解)
4. [全局选项](#全局选项)
5. [数据库支持](#数据库支持)
6. [输出格式](#输出格式)
7. [实用示例](#实用示例)
8. [常见问题](#常见问题)

---

## 安装

### 前置要求

- Node.js 18.0 或更高版本
- npm 或 yarn

### 安装步骤

```bash
# 克隆仓库
git clone https://github.com/your-repo/ncbi-database-skill.git
cd ncbi-database-skill

# 安装依赖
npm install

# 运行 CLI
node bin/cli.js --help

# 或全局安装
npm link
```

---

## 快速开始

### 1. 搜索基因

```bash
# 搜索人类 BRCA1 基因
node bin/cli.js search gene "BRCA1[gene] AND Homo sapiens[organism]"
```

### 2. 获取基因摘要

```bash
# 获取基因 ID 672 的摘要
node bin/cli.js summary gene 672
```

### 3. 获取序列

```bash
# 获取核酸序列（FASTA 格式）
node bin/cli.js fetch nucleotide NM_001385642 -o json

# 获取蛋白质序列
node bin/cli.js fetch protein NP_000001
```

### 4. 链接查询

```bash
# 查找基因关联的 PubMed 文献
node bin/cli.js link gene 672 pubmed

# 查找蛋白质关联的基因
node bin/cli.js link protein NP_000001 gene
```

### 5. 数据库信息

```bash
# 查看基因数据库信息
node bin/cli.js info gene

# 查看 PubMed 数据库信息
node bin/cli.js info pubmed
```

---

## 命令详解

### search (s) - 搜索命令

在 NCBI 数据库中搜索记录。

```bash
ncbi search <database> <search_term> [options]
```

**示例：**

```bash
# 搜索基因
ncbi search gene "BRCA1[gene]"

# 搜索 PubMed（标题中包含 cancer）
ncbi search pubmed "cancer[title]" -d 10

# 搜索蛋白质
ncbi search protein "hemoglobin[protein name]"
```

**选项：**
- `-n, --retmax <number>` - 返回结果数量（默认：20）
- `-d, --delay <ms>` - 请求延迟

---

### fetch (f, efetch) - 获取记录

通过 ID 获取完整记录。

```bash
ncbi fetch <database> <ids> [options]
```

**示例：**

```bash
# 获取基因记录
ncbi fetch gene 672

# 获取多条记录
ncbi fetch gene 672,675,676

# 指定输出格式
ncbi fetch protein NP_000001 -o json
ncbi fetch nucleotide NM_001385642 -o xml
```

**选项：**
- `-o, --output <format>` - 输出格式：json、xml、text

---

### summary (sum, esummary) - 摘要查询

获取记录的快速摘要信息。

```bash
ncbi summary <database> <ids> [options]
```

**示例：**

```bash
# 获取基因摘要
ncbi summary gene 672,675

# 获取 PubMed 文章摘要
ncbi summary pubmed 12345678
```

---

### link (l, elink) - 链接查询

查找关联记录。

```bash
ncbi link <source_db> <ids> <target_db> [options]
```

**示例：**

```bash
# 基因 -> PubMed 文献
ncbi link gene 672 pubmed

# 蛋白质 -> 基因
ncbi link protein NP_000001 gene

# 核酸 -> 蛋白质
ncbi link nucleotide NM_001385642 protein
```

---

### info (i, einfo) - 数据库信息

查看 NCBI 数据库的元信息。

```bash
ncbi info <database>
```

**示例：**

```bash
# 查看可用数据库
ncbi info gene
ncbi info pubmed
```

---

### assembly (asm) - 组装名称解析

将常见组装名称转换为 RefSeq accession。

```bash
ncbi assembly <assembly_name>
```

**示例：**

```bash
# 人类参考基因组
ncbi assembly GRCh38
ncbi assembly "GRCh38.p14"

# 小鼠基因组
ncbi assembly mm10
ncbi assembly mm39

# 大鼠基因组
ncbi assembly rn7
```

**支持的部分组装名称：**
| 输入 | 输出 |
|------|------|
| GRCh38 | GCF_000001405.40 |
| GRCh37 | GCF_000001405.14 |
| mm39 | GCF_000001635.10 |
| mm10 | GCF_000001635.4 |
| rn7 | GCF_016699045.2 |

---

### gene-panorama (gp) - 基因全景

获取基因信息及关联的 PubMed 文献。

```bash
ncbi gene-panorama <gene_id_or_symbol>
```

**示例：**

```bash
# 通过基因符号查询
ncbi gene-panorama BRCA1
ncbi gene-panorama TP53

# 通过基因 ID 查询
ncbi gene-panorama 672
```

**返回信息：**
- 基因基本信息（ID、符号、描述、染色体位置）
- 关联 PubMed 文章数量
- 最新 PubMed 文章列表（最多 10 篇）

---

### variant (var) - 变异查询

查询 ClinVar/dbsnp 中的临床变异信息。

```bash
ncbi variant <variant_id>
```

**示例：**

```bash
# 通过 rs 号查询
ncbi variant rs123456
ncbi variant rs699

# 通过 ClinVar ID 查询
ncbi variant SCV000123456
```

**返回信息（ClinVar）：**
- 临床意义（Benign、Pathogenic 等）
- 审查状态
- 相关疾病
- 变异类型
- 相关基因

---

### blast - BLAST 序列搜索

进行序列相似性搜索。

```bash
ncbi blast <sequence> [options]
```

**示例：**

```bash
# 核酸 BLAST
ncbi blast "ATCG..." -d nucleotide

# 蛋白质 BLAST
ncbi blast "MSEQ1" -d protein

# 指定程序
ncbi blast "ATCG..." --program blastn
```

**选项：**
- `-d, --database <db>` - 搜索数据库（默认：nt）
- `--program <program>` - BLAST 程序（默认：megablast）
  - `blastn` - 核酸 vs 核酸
  - `blastp` - 蛋白质 vs 蛋白质
  - `blastx` - 核酸翻译 vs 蛋白质

---

### sra - SRA 信息查询

获取 SRA（高通量测序存档）实验信息。

```bash
ncbi sra <sra_id>
```

**示例：**

```bash
# 通过 SRR ID 查询
ncbi sra SRR123456

# 通过项目 ID 查询
ncbi sra PRJNA123456

# 通过实验 ID 查询
ncbi sra SRX123456
```

---

### espell - 拼写检查

检查 PubMed 搜索词的拼写。

```bash
ncbi espell <term>
```

**示例：**

```bash
# 检查拼写
ncbi espell "brca1"
ncbi espell "crispr cas9"
```

---

### ecitmatch - 引用匹配

将文献引用匹配到 PubMed 记录。

```bash
ncbi ecitmatch <citation>
```

**示例：**

```bash
# 作者+期刊格式
ncbi ecitmatch "Smith J, Nature 2020"

# PMID 格式
ncbi ecitmatch "PMID:12345678"
```

---

## 全局选项

| 选项 | 说明 | 默认值 |
|------|------|---------|
| `-d, --delay <ms>` | 请求间隔毫秒数 | 100ms（有 API key 时 10ms）|
| `-o, --output <format>` | 输出格式 | json |
| `-k, --apikey <key>` | NCBI API Key | - |
| `-v, --verbose` | 详细输出模式 | false |
| `-h, --help` | 显示帮助信息 | - |

---

## 数据库支持

常用数据库速查：

| 数据库 | 命令参数值 | 说明 |
|--------|------------|------|
| 基因 | `gene` | 基因信息 |
| 蛋白质 | `protein` | 蛋白质序列 |
| 核酸 | `nucleotide`, `nuccore` | 核酸序列 |
| PubMed | `pubmed` | 文献摘要 |
| Taxonomy | `taxonomy` | 分类信息 |
| SNP | `snp` | 单核苷酸多态性 |
| ClinVar | `clinvar` | 临床变异 |
| Assembly | `assembly` | 基因组组装 |
| Structure | `structure` | 3D 结构 |
| SRA | `sra` | 测序原始数据 |

---

## 输出格式

### JSON（默认）

```bash
# 最适合程序化处理
ncbi summary gene 672 -o json
```

### XML

```bash
# 适合详细数据结构
ncbi fetch nucleotide NM_001385642 -o xml
```

### Text/FASTA

```bash
# 适合序列数据
ncbi fetch nucleotide NM_001385642 -o text
```

---

## 实用示例

### 工作流程 1：查找基因 → 获取序列

```bash
# 1. 搜索基因
ncbi search gene "BRCA1[gene] AND Homo sapiens[organism]"

# 2. 提取 ID（假设得到 672）

# 3. 查找关联的核酸序列
ncbi link gene 672 nucleotide

# 4. 获取序列
ncbi fetch nucleotide <sequence_id> -o fasta
```

### 工作流程 2：查找基因 → 查找文献

```bash
# 1. 获取基因 ID
ncbi search gene "TP53[gene]"

# 2. 链接到 PubMed
ncbi link gene 7157 pubmed

# 3. 获取文献摘要
ncbi summary pubmed <pubmed_ids>
```

### 工作流程 3：获取基因完整信息

```bash
# 使用 gene-panorama 一步获取基因+文献
ncbi gene-panorama BRCA1
```

### 工作流程 4：查询变异临床意义

```bash
# 查询 rs 号
ncbi variant rs699
ncbi variant rs4899059

# 查询 ClinVar ID
ncbi variant RCV000123456
```

---

## 速率限制

- **无 API Key**: 3 请求/秒
- **有 API Key**: 10 请求/秒

### 获取 API Key

1. 访问 https://www.ncbi.nlm.nih.gov/account/
2. 注册/登录
3. 在设置中启用 API 访问

### 使用 API Key

```bash
# 通过命令行参数
ncbi search gene "BRCA1" -k YOUR_API_KEY

# 或设置环境变量
export NCBI_API_KEY=YOUR_API_KEY
```

---

## 常见问题

### Q: 如何提高请求速率？

A: 申请 NCBI API Key 并使用 `-k` 参数，或在代码中设置。

### Q: 为什么请求失败？

A: 检查：
1. 网络连接
2. API Key 是否有效
3. 请求参数是否正确
4. 是否超过速率限制

### Q: 如何处理大结果集？

A: 使用 `retmax` 和 `retstart` 参数进行分页：
```bash
# 获取前 100 条
ncbi search pubmed "cancer" -n 100

# 获取第 101-200 条
ncbi search pubmed "cancer" -n 100 --retstart 100
```

### Q: 支持哪些输出格式？

A: JSON、XML、Text（FASTA/GenBank）

---

## 相关链接

- [NCBI E-utilities 文档](https://www.ncbi.nlm.nih.gov/books/NBK25497/)
- [API 参考](https://www.ncbi.nlm.nih.gov/books/NBK25501/)
- [NCBI EDirect 指南](https://www.ncbi.nlm.nih.gov/books/NBK25500/)
