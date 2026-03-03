# 社媒热榜数据源接入指南

本文件记录分析时可调用的**实时社媒热榜**数据源，包含接入方案、调用示例与注意事项。执行选题分析时，优先在此获取「社交传播中」的热点素材，再结合搜索引擎做深度核查。

---

## 总体思路：三层数据叠加

| 层级 | 数据来源 | 作用 | 优先级 |
|------|---------|------|--------|
| **第一层：热榜聚合** | DailyHotApi 公开实例（国内）+ Reddit JSON（国外）| 抓「正在传播」的标题，批量扫描 | ⭐⭐⭐ 最优先 |
| **第二层：平台热榜官网** | tophub.today 直接浏览 / 各平台热搜页 | 带热度值、浏览标题趋势 | ⭐⭐ 次之 |
| **第三层：搜索引擎核查** | Google/Bing + 专业媒体 | 验证信源、补充细节 | ⭐ 最终核查 |

---

## 一、国内社媒热榜

### 1-A DailyHotApi 公开实例（首选，无需任何认证）

> 开源项目：https://github.com/imsyy/DailyHotApi  
> 公开 API 实例：`https://api-hot.imsyy.top/`

**直接调用，返回 JSON，无需注册、无需 API Key，5 分钟缓存更新一次。**

#### 关键路由

| 平台 | 路由 | 说明 |
|------|------|------|
| 微博热搜 | `https://api-hot.imsyy.top/weibo` | 微博热搜榜 TOP50 |
| 抖音热点 | `https://api-hot.imsyy.top/douyin` | 抖音热点榜 |
| 快手热榜 | `https://api-hot.imsyy.top/kuaishou` | 快手热点榜 |
| B站热门 | `https://api-hot.imsyy.top/bilibili` | B站热门榜 |
| 知乎热榜 | `https://api-hot.imsyy.top/zhihu` | 知乎热榜 |
| 今日头条 | `https://api-hot.imsyy.top/toutiao` | 头条热榜 |
| 百度热搜 | `https://api-hot.imsyy.top/baidu` | 百度热搜 TOP |
| 小红书 | `https://api-hot.imsyy.top/xiaohongshu` | 小红书热榜（若支持） |
| 全部平台 | `https://api-hot.imsyy.top/all` | 所有平台热榜合并返回 |

**加 `/new` 强制跳过缓存**（如：`https://api-hot.imsyy.top/weibo/new`）

#### 返回字段（每条热点）

```json
{
  "title": "标题",
  "url": "原文链接",
  "hot": "12345 热度值",
  "cover": "封面图URL",
  "desc": "简介（部分平台有）",
  "timestamp": 1709000000
}
```

#### Agent 调用建议（适合在分析工作流中使用）

使用 browser 工具或 WebFetch 工具调用上述 URL，获取 JSON 后提取 `title` + `hot` 字段，按热度降序排列，优先取前 20 条作为候选选题池。

---

### 1-B 今日热榜官方 API / 榜眼数据（需注册 Access Key）

> 注册地址：https://www.tophubdata.com/register  
> API 文档：https://www.tophubdata.com/documentation

注册后免费获取 Access Key，通过 Header 传递认证：`Authorization: YOUR_ACCESS_KEY`

#### 核心接口

| 用途 | 地址 | 说明 |
|------|------|------|
| 全站热点TOP100 | `GET https://api.tophubdata.com/hot?date=YYYY-MM-DD` | **榜中榜**，跨平台综合热度最高的100条，最适合快速扫题 |
| 微博热搜 | `GET https://api.tophubdata.com/nodes/KqndgxeLl9` | 微博 hashid |
| 知乎热榜 | `GET https://api.tophubdata.com/nodes/mproPpoq6O` | 知乎 hashid |
| 全部榜单列表 | `GET https://api.tophubdata.com/nodes?p=1` | 获取所有平台 hashid 索引 |
| 跨平台关键词搜索 | `GET https://api.tophubdata.com/search?q=关键词` | 全网热点关键词检索 |

#### 常用平台 hashid 参考

| 平台 | hashid |
|------|--------|
| 微博热搜 | KqndgxeLl9 |
| 知乎热榜 | mproPpoq6O |
| 抖音热点 | 可通过 /nodes 接口查询 |
| B站热门 | 可通过 /nodes 接口查询 |

> 提示：今日热榜网页 URL `https://tophub.today/n/{hashid}` 与 API hashid 完全一致，可直接从网页 URL 中取用。

---

### 1-C 今日热榜网站（无 API Key 时备用）

> 直接访问：https://tophub.today

浏览器可见所有平台热榜。分析时可用 WebFetch 抓取页面文本，或让 browser 工具访问并截取热点标题列表。

---

## 二、国外社媒热榜

### 2-A Reddit 公开 JSON（完全免费，无需认证）

Reddit 所有公开页面支持加 `.json` 后缀直接返回结构化数据，**无需任何 API Key**。

#### 关键 URL

| 用途 | URL |
|------|-----|
| 全站热帖（本周热门） | `https://www.reddit.com/r/popular.json?limit=50` |
| 全站热帖（本日上升） | `https://www.reddit.com/r/all/rising.json?limit=50` |
| 全站热帖（今日最热） | `https://www.reddit.com/r/all/hot.json?limit=50` |
| 全站本周 TOP | `https://www.reddit.com/r/all/top.json?t=week&limit=50` |
| 指定话题热帖 | `https://www.reddit.com/r/worldnews/hot.json?limit=25` |

**加请求头 `User-Agent: Mozilla/5.0 compatible` 可避免 429 限流。**

#### 返回字段（每条帖子 data 内）

```json
{
  "title": "标题",
  "url": "外链URL",
  "score": 42000,
  "num_comments": 3200,
  "subreddit": "worldnews",
  "created_utc": 1709000000,
  "selftext": "正文（若有）",
  "thumbnail": "缩略图URL"
}
```

> `score`（点赞数）+ `num_comments`（评论数）= 综合情绪热度指标，二者都高说明「能吵起来」。

---

### 2-B YouTube 热门视频（Google API Key，免费配额 10,000 单位/天）

> 申请地址：https://console.cloud.google.com → 启用 YouTube Data API v3

#### 调用示例

```
GET https://www.googleapis.com/youtube/v3/videos
  ?part=snippet,statistics
  &chart=mostPopular
  &regionCode=US
  &maxResults=20
  &key=YOUR_API_KEY
```

将 `regionCode` 换成 `KR` / `JP` / `GB` 等可查看各地热门。

#### 适用场景

专门检索「有没有正在发酵的视频素材」，如发布会 clip、街头事件、病毒视频——对「视觉素材可得性」评分有直接帮助。

---

### 2-C TrendsOnX（X/Twitter 热榜，免费 tier）

> 服务地址：https://trendsonx.com/

提供 REST API，免费 tier 有速率限制，返回指定地区 X 趋势话题。

```
GET https://api.trendsonx.com/v1/trends?location=worldwide
Authorization: Bearer YOUR_FREE_KEY
```

注：免费 tier 可获得全球/美国/英国等地区热门 Trending Topics，带 tweet volume。

---

### 2-D Google Trends（非官方 pytrends 库）

> 安装：`pip install pytrends`  
> 文档：https://github.com/GeneralMills/pytrends

```python
from pytrends.request import TrendReq
pytrends = TrendReq()
trending = pytrends.trending_searches(pn='united_states')  # 或 china
print(trending)
```

对 AI agent 工作流而言，更推荐直接调用 `trending_searches()`，无需 API Key，返回当日趋势关键词 DataFrame。

---

## 三、分析工作流中的调用顺序建议

以下是在执行「狐扯电台热点选题」分析时，调取社媒热榜数据的推荐顺序：

```
步骤 1【国内批量扫题】
  → WebFetch: https://api-hot.imsyy.top/weibo/new        （微博热搜）
  → WebFetch: https://api-hot.imsyy.top/douyin/new        （抖音热点）
  → WebFetch: https://api-hot.imsyy.top/bilibili/new       （B站热门）
  → WebFetch: https://api-hot.imsyy.top/zhihu/new          （知乎热议）
  提取各榜 TOP20 标题，合并去重，按热度降序初筛

步骤 2【国外批量扫题】
  → WebFetch: https://www.reddit.com/r/all/hot.json?limit=50
  → WebFetch: https://www.reddit.com/r/worldnews/hot.json?limit=25
  提取 title + score + num_comments，按 score 降序初筛

步骤 3【候选池五维评估】
  对合并后的候选标题，按「信息差·情绪·争议·素材·安全」五维评分

步骤 4【搜索引擎核查】
  对评分靠前的候选选题，用 WebSearch 进行信源核查与细节补充

步骤 5【撰写周报】
  按 fox-radio.md 输出格式生成报告
```

---

## 四、访问失败时的降级策略

| 数据源 | 失败备选 |
|--------|---------|
| DailyHotApi 公开实例挂了 | 直接访问 tophub.today 页面（WebFetch 抓文本） |
| Reddit JSON 被限流（429） | 加 User-Agent Header 重试；或访问 old.reddit.com/r/popular.json |
| YouTube API 配额耗尽 | 用 WebSearch「site:youtube.com trending」替代 |
| TrendsOnX 不可用 | 访问 https://twitter.com/explore（需 browser 工具） |

---

## 五、免费额度与费用速查

| 数据源 | 免费方案 | 付费门槛 |
|--------|---------|---------|
| DailyHotApi 公开实例 | 完全免费，无限制（公益实例） | 自建无费用 |
| 今日热榜 榜眼数据 API | 注册后有免费额度（具体见控制台） | 按量付费 |
| Reddit JSON | 完全免费（官方公开 API） | 官方 OAuth API 付费 |
| YouTube Data API v3 | 10,000 单位/天免费 | $0.006/1000 单位 |
| TrendsOnX | 免费 tier（有速率限制） | 订阅制 |
| Google Trends (pytrends) | 完全免费（非官方） | 无付费选项 |

---

## 六、小红书热榜说明

小红书目前无公开 API 或可靠的第三方聚合接口，官方封锁了大部分爬虫路径。  
**可行替代方案**：
1. 浏览 `https://www.xiaohongshu.com/explore`（需登录），用 browser 工具截取「发现」页热门话题；
2. 搜索「小红书 热门话题 本周」通过搜索引擎间接了解；
3. DailyHotApi 若后续支持小红书，路由为 `https://api-hot.imsyy.top/xiaohongshu`。
