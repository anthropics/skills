# 引擎速查（Claude 排障用）

引擎是 AdFlow v0.2（本地剪辑引擎），源码在 `engine/adflow/`。skill 的无头路径只走确定性模块，不碰任何 LLM API。

## 一、出片流水线（custom_text 路径）

```
文案.txt
  → 断句建分镜（每句一镜，标点切分，无 LLM）        pipeline._scripts_from_plain_text
  → 配音合成（edge 免费 / volcano / minimax）        engine/tts_engine.py 等
  → 素材匹配（标签过滤+评分排序，无 LLM）             agents/match_agent.py
  → 渲染（ffmpeg 剪辑 + 字幕 + 可选 BGM + 调色）      engine/variant_factory.py
  → 本地广告法检查                                    compliance/ad_law_checker.py
  → engine/output/*.mp4
```

- 出 N 条 = 同文案深拷 N 份脚本，配音男女交替 × 画面跨条去重
- 镜头角色：第一句 hook、中间 product_demo、最后一句 cta

## 二、make_videos.py 参数

| 参数 | 默认 | 说明 |
|---|---|---|
| --text-file / --text | 必填 | 文案（推荐 --text-file） |
| --product-name | 我的产品 | 内部记录+命名用 |
| --category | 空 | 产品类目，影响自动时长 |
| --count | 3 | 出几条 |
| --platform | ocean_engine | douyin/xiaohongshu/kuaishou/shipinhao/ocean_engine |
| --voice | 空=自动交替 | 音色名见 tts-setup.md |
| --rate | 0=默认 | 语速 0.9 慢 / 1.1 快 |
| --aspect | portrait | 竖屏/横屏 |
| --duration | 0=自动 | 目标时长秒 |
| --prefix | 空 | 文件名前缀 |
| --bgm | 空=轮换 | 指定 BGM 文件 |
| --force | 关 | 已出的成品也全部重出（默认同参数重跑沿用已验过的成片只补缺） |

### 输出协议（跑完看什么）

- 成片清单标记块：`===VIDEOS_START===` 里逐条 `FILE=路径` + `STATUS=OK|SKIP|FAIL` + `COMPLIANCE=PASS/FAIL`（OK=本次新出，SKIP=断点续跑沿用旧成片；出片失败时块里只有 `FAILED_STAGE=` 指明挂在哪一步）
- 跑完自动成片体检（verify_output.py 同款检查），结尾 `VERIFY_PASS=n/m`
- 退出码：0 全过 / 1 出片失败（看 FAILED_STAGE）/ 2 有成片没过体检 / 130 手动停
- 体检单独重跑：`python scripts/verify_output.py --dir engine/output`（详细判定项见该文件头注释）

### 断点续跑（怎么少干重复活）

- 账本 `engine/output/.make_videos_ledger.json` 按参数指纹（文案+产品+平台+画面比例等，**不含 --count**）记每组任务已出的成片
- 重跑同命令：账本里体检还过的旧成片直接 SKIP 沿用，只补缺的；`--count` 加大只补增量；上次没过体检/被删/损坏的条目自动重出
- 渲染中途打断（断电/Ctrl+C）的半条不在账本里，重跑会重出（引擎按条渲染，打断的条不算数）
- 想全部重出（比如改了 config 效果）加 `--force`；账本删掉等于全部重出

## 三、素材库与标签

- 库：`engine/data/adflow.db`（SQLite）。清空重导 = 删这文件
- 打标 15 维度的枚举值以 `scripts/apply_tags.py` 文件头注释为准（与引擎 Vision 打标同构）
- 匹配优先用 scene/shot_type/product_visibility 等结构化标签 + free_tags；未打标素材也能被匹配（兜底全库），但画面相关性差
- 竖屏出片只用竖素材（h≥w 即算竖），竖素材不足自动放行高清横素材裁切

## 四、config.yaml 常动开关

skill 版已调好的默认（不用动）：`tts.backend: edge`、`segmentation.enabled: false`（标点断句）、`diversity.match_weights.semantic: 0`（免装 CLIP）、`digital_human.enabled: false`。

| 键 | 作用 |
|---|---|
| tts.backend | edge（免费）/ volcano / minimax |
| tts.speech_rate | 全局语速（默认 1.1） |
| editing.default_resolution | 输出分辨率（默认 1080x1920） |
| editing.subtitle.font_size | 字幕字号（默认 56） |
| editing.subtitle.cta_color | 结尾 CTA 句字幕色（默认 white；改红色 #FF4444 在红/暖色素材上会看不见） |
| editing.shot_duration_ms | 每镜默认时长（默认 2500） |
| bgm.enabled | 是否自动配乐（默认 true，空库等于没配乐） |
| compliance.check_ad_law | 广告法检查开关（保持 true） |

## 五、常见报错对照

| 报错/现象 | 原因 → 处理 |
|---|---|
| `ffmpeg not found` / 渲染段空 | 没装 ffmpeg → `python setup_env.py --ffmpeg` |
| `No module named xxx` | 依赖没装全 → `python setup_env.py --deps` |
| edge-tts 超时 / `NoAudioReceived` | 微软接口网络抖动 → 重跑一次；连发多条失败换网络或考虑付费方案 |
| 配音 401/403 | 付费方案 key 错/过期 → 对照 tts-setup.md 重配 |
| `素材库是空的` | 没导素材 → import_materials.py |
| 成片画面重复多 | 素材太少（<3 条）或太短（<2s 降权）→ 补素材 |
| 合规检查未过 | 文案触禁语（输出会指明词）→ 改词重出 |
| 退出码 2 / 体检 FAIL | 黑帧→素材坏换素材；无声→配音丢重跑；时长不足→文案太短；方向不对→查 --aspect |
| 退出码 1 / FAILED_STAGE=xxx | xxx 是最后一条进度（配音/素材匹配/渲染变体…），挂哪补哪；重跑同命令只补缺的 |
| 渲染卡在 0% 很久 | 正常，TTS 和渲染按条进行，一条几分钟 |
| moviepy 内存报错 | 单条素材过大（>500MB）→ 切小再导 |

## 六、目录

```
engine/
  adflow/            引擎源码（agents/engine/db/gui/compliance/...）
  main.py            可选图形界面（python main.py）
  config.yaml        全局配置
  .env               付费配音 key（用户自建，不随包分发）
  materials/         视频素材库
  bgm_library/       背景 Music（用户自有授权）
  data/              数据库+关键帧
  output/            成片（含 _filter_reports 合规报告）
```
