# ncbi-database

通过命令行界面 (CLI) 查询和获取 NCBI 数据库数据，使用 E-utilities Entrez API。

## 何时使用

- 从 Gene 数据库查询基因信息
- 从 Nucleotide (GenBank, RefSeq) 获取 DNA/RNA 序列
- 从 Protein 数据库获取蛋白质序列
- 获取分类信息和谱系
- 搜索和获取 PubMed 文献
- 查询 dbSNP、ClinVar 的遗传变异
- 访问基因组组装和注释
- 批量下载大型数据集

## 安装与运行

```bash
# 直接使用 npx 运行（推荐）
npx ncbi-database search gene "BRCA1[gene]"

# 或全局安装
npm install -g ncbi-database
ncbi search gene "BRCA1[gene]"
```

## 命令

### search (s)

搜索 NCBI 数据库，返回 ID 列表。

```bash
ncbi search <database> <term> [options]
```

**示例：**

```bash
# 搜索人类 BRCA1 基因
ncbi search gene "BRCA1[gene] AND Homo sapiens[organism]" -d 10

# 搜索 PubMed 文献
ncbi search pubmed "CRISPR[title] AND 2023[dp]" -d 10
```

### fetch (f, efetch)

获取记录详情。

```bash
ncbi fetch <database> <id> [options]
```

**示例：**

```bash
# 获取基因记录 (JSON)
ncbi fetch gene 672 -o json

# 获取 DNA 序列 (FASTA)
ncbi fetch nucleotide NM_001385642 -o text

# 获取蛋白质序列 (FASTA)
ncbi fetch protein NP_000492 -o text
```

### summary (sum, esummary)

获取文档摘要。

```bash
ncbi summary <database> <id> [options]
```

**示例：**

```bash
# 获取基因摘要
ncbi summary gene 672 -o json

# 获取 PubMed 文章摘要
ncbi summary pubmed 12345678 -o json
```

### link (l, elink)

查找数据库之间的链接记录。

```bash
ncbi link <database> <id> <target_db> [options]
```

**示例：**

```bash
# 查找基因的 PubMed 链接
ncbi link gene 672 pubmed -d 10

# 查找 PubMed 的基因链接
ncbi link pubmed 12345678 gene
```

### info (i, einfo)

获取数据库元数据信息。

```bash
ncbi info <database>
```

**示例：**

```bash
ncbi info gene
ncbi info pubmed
ncbi info protein
```

## 全局选项

| 选项                | 简写  | 描述                    | 默认值                   |
| ----------------- | --- | --------------------- | --------------------- |
| --delay <ms>      | -d  | 请求间隔毫秒数               | 100ms (有API key可10ms) |
| --output <format> | -o  | 输出格式: json, xml, text | json                  |
| --apikey <key>    | -k  | NCBI API Key          | -                     |
| --help            | -h  | 显示帮助信息                | -                     |
| --verbose         | -v  | 详细输出模式                | -                     |

## 支持的数据库

| 数据库        | 命令中写法               | 描述                           |
| ---------- | ------------------- | ---------------------------- |
| gene       | gene                | 基因记录及注释                      |
| nucleotide | nucleotide, nuccore | DNA、RNA 序列 (GenBank, RefSeq) |
| protein    | protein             | 蛋白质序列                        |
| taxonomy   | taxonomy            | 分类树                          |
| pubmed     | pubmed              | 生物医学文献 (MEDLINE)             |
| snp        | snp                 | 单核苷酸多态性 (dbSNP)              |
| clinvar    | clinvar             | 临床变异                         |
| genome     | genome              | 基因组记录                        |
| assembly   | assembly            | 基因组组装                        |
| structure  | structure           | 大分子结构 (MMDB)                 |
| geo        | geo, gds            | 基因表达 omnibus                 |
| sra        | sra                 | 序列读数档案                       |

## 速率限制

- **无 API Key**: 3 请求/秒
- **有 API Key**: 10 请求/秒

获取 API Key: https://www.ncbi.nlm.nih.gov/account/

```bash
# 使用 API Key
ncbi search gene "BRCA1[gene]" -k YOUR_API_KEY -d 10
```

## 使用示例

### 1. 搜索人类基因

```bash
ncbi search gene "BRCA1[gene] AND Homo sapiens[organism]" -d 10
```

### 2. 获取基因摘要

```bash
ncbi summary gene 672 -o json
```

### 3. 获取 DNA 序列

```bash
ncbi fetch nucleotide NM_001385642 -o text
```

### 4. 搜索 PubMed 文献

```bash
ncbi search pubmed "CRISPR[title] AND review[pt] AND 2023[dp]" -d 10
```

### 5. 查找基因的 PubMed 链接

```bash
ncbi link gene 672 pubmed -d 10
```

### 6. 获取数据库信息

```bash
ncbi info gene
```

## 错误处理

| 错误码 | 描述    | 解决方案            |
| --- | ----- | --------------- |
| 400 | 请求错误  | 检查参数语法          |
| 429 | 请求过多  | 添加 API Key，实施退避 |
| 503 | 服务不可用 | 指数退避重试          |
| 空结果 | 无匹配   | 检查搜索词拼写         |

## 更多信息

- NCBI E-utilities: https://www.ncbi.nlm.nih.gov/books/NBK25497/
- Entrez Programming Utilities: https://www.ncbi.nlm.nih.gov/books/NBK25501/
- NCBI API Keys: https://www.ncbi.nlm.nih.gov/account/
