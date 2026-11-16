---
name: adflow-infoflow-video
description: 想投广告不会剪视频？给产品素材，它写文案、配音、混剪、加字幕，几分钟出 3 条能直接投的带货短视频。广告法禁词自动查，全程不用剪辑软件、不用 API key。触发词：信息流素材、电商投放素材、带货短视频、批量出片、裂变视频、广告混剪。
display_name: 带货广告视频自动出片（配音混剪全包）
display_name_en: Auto Ad Video Maker
description_zh: 给产品素材，自动写文案、配音、混剪、加字幕，几分钟出 3 条能直接投的带货短视频。
description_en: Turn product clips into ready-to-run ad videos with copy, voiceover and subtitles in minutes.
examples_zh:
- "帮我把这批产品视频剪成带货广告"
- "出 3 条不同文案的投放素材"
- "查一下这条广告有没有违禁词"
examples_en:
- "Cut these clips into shopping ad videos"
- "Make 3 ad variants with different copy"
- "Check my ad script for banned words"
version: 1.4.4
author: "ayan"
---

# AdFlow 信息流广告混剪出片

你（Claude）在这个 skill 里的角色：**策划 + 质检员**。写文案、看图打标签、把关合规是你的活；配音、剪片、渲染全部交给本地引擎脚本跑。**任何一步都不需要调外部大模型 API。**

## 硬性红线（每次开工前自查，违反就停）

1. **素材版权**：动手导入素材前必须问一句「这些视频素材都是你自己拍的，或者拿到了使用授权吗？」用户否认或含糊 → 拒绝用这批素材出片，说明侵权风险。
2. **BGM 版权**：只允许用户自己提供有授权的音乐（放进 `engine/bgm_library/`）。绝不给用户找下载链接、不推荐盗版音乐源。engine 默认不带任何音乐，没音乐也能出片。
3. **广告法**：写文案时执行 [references/compliance.md](references/compliance.md) 的禁用语清单（最/第一/国家级/根治/保证赚钱这类绝对化和功效承诺词全禁）。引擎渲染后还会跑一道本地广告法检查，未过的片要改文案重出。
4. **品类红线**：药品/医疗器械/保健食品功效宣传、金融投资回报、烟草、代刷代办这类活，直接拒绝，不接单。
5. **不碰别人成果**：不下载、不扒别人的视频当素材；「复制爆款」指的是复制结构和节奏，不是搬运画面。

## 工作流程

按顺序走，每一步做完确认没问题再进下一步。用户是纯小白时，把你要做的事用一句话说清楚再动手（例：「我先检查你电脑的环境，大概半分钟」）。

### 第 0 步：解压引擎 + 环境体检（首次必做）

先解压引擎（`engine/adflow/` 已存在就跳过）：Windows PowerShell 跑 `Expand-Archive engine/adflow-engine.zip engine/ -Force`；Mac/Linux 跑 `unzip engine/adflow-engine.zip -d engine/`。然后体检：

```bash
python scripts/check_env.py
```

- 全 [OK] → 跳到第 1 步。
- 有 [X] → 按输出里的「怎么修」处理：
  - 缺依赖 / 缺 ffmpeg → `python scripts/setup_env.py --all`（装依赖走清华镜像，ffmpeg 约 80MB 要下载一会）
  - 用户电脑连 Python 都没有 → 打开 [references/beginner-guide.md](references/beginner-guide.md)，照着「装 Python」一节一步步带用户装（python.org 下载，勾选 Add to PATH）。
- 用户提问看不懂报错 → 截图/复制报错给你，你对照 [references/engine-reference.md](references/engine-reference.md) 的「常见报错」一节解释。

### 第 1 步：配音方案（首次问一次，之后记住选择）

问用户（就这一句，别展开）：

> 配音用哪种？
> A. 微软免费配音（推荐，不用注册不用 key，效果不错）
> B. 火山引擎配音（音质更像真人，要注册账号，按量付费）
> C. MiniMax 配音（情感表现好，要注册账号，按量付费）

- 选 A（默认）：什么都不用配，config 已设好 `tts.backend: edge`，直接下一步。
- 选 B/C：打开 [references/tts-setup.md](references/tts-setup.md)，带用户走对应教程（注册 → 拿 key → 写进 `engine/.env` → 改 `engine/config.yaml` 的 backend）→ 跑 `check_env.py` 确认显示「key 已配置」。
- 之后每次出片不用再问。换音色参考 tts-setup.md 的音色表（`make_videos.py --voice`）。

### 第 2 步：导入素材 + 打标签

先过红线 1（版权问话），然后：

```bash
python scripts/import_materials.py --dir "用户的素材文件夹"
```

脚本会把视频拷进 `engine/materials/`、探测信息入库、每条抽 4 张关键帧，清单落在 `engine/data/keyframes/manifest.json`。

然后**你来看图打标签**（这就是别人家要调 Vision API 的活，你直接干）：

1. 读 `engine/data/keyframes/manifest.json`
2. 用 Read 工具逐条看关键帧图片（`data/keyframes/<素材ID>/f1.jpg` ~ `f4.jpg`）
3. 按 [scripts/apply_tags.py](scripts/apply_tags.py) 文件头注释里的 15 个维度写标签（枚举值必须一字不差，free_tags 写 5~10 个中文词描述画面内容）
4. 全部写进 `engine/data/keyframes/tags.json`（JSON 数组，每条带 material_id）

```bash
python scripts/apply_tags.py
```

素材很多时（>30 条）可以分批：先处理一部分，标签质量优先。素材极少（<3 条）时提醒用户多备些素材，画面才够换。

### 第 3 步：写文案（你的主战场）

用户给了爆款参考（视频或文案）→ 先按 [references/hit-teardown-template.md](references/hit-teardown-template.md) 拆出可复用因子再仿写（只学结构节奏，画面原声一律不搬）。

按产品信息 + 目标平台写口播文案，方法论照 [references/copywriting-playbook.md](references/copywriting-playbook.md)（六型选型、钩子十法、节奏、情绪曲线都在里面）。硬规则：

- 8~12 句、全文 120~150 字，撑 22~30 秒（引擎按句切镜头，一句一个镜头）
- 口播短句一句 ≤15 字为目标，一句说清一件事；意思必须完整，绝不为了凑短把话拦腰截断
- 第一句是钩子，最后一句是行动号召；按平台调风格：竖屏快节奏 / 种草闺蜜感 / 直爽接地气 / 温和叙事（引擎 config 里有五平台风格表，--platform 参数选）
- 写完跑 playbook 第五节的爆款潜质自检清单，命中不到 3 条先重写，不达标不给用户看
- 再自查红线 3（广告法禁语 + 替换原则 + 价格带规格），然后给用户确认：「文案如下，改哪句直接说，没问题我就开始出片」

用户自带文案时跳过创作，只做合规自查和断句检查（超长句提醒拆短，拆句同样保证每句意思完整）。

### 第 4 步：出片

用户确认文案后存成文件再跑（文案放引号里容易踩转义坑）：

```bash
python scripts/make_videos.py --text-file 文案.txt --product-name 产品名 --count 3 --platform douyin
```

- `--count` 默认 3：同一文案出多条，配音和画面组合不同（裂变）
- **断点续跑**：重跑同一条命令，上次已出且体检过的成片直接沿用（STATUS=SKIP），只补缺的条目（含上次没过体检的）；`--count` 加大也只补增量。全部重出加 `--force`
- 跑的时长几分钟，期间把进度念给用户听（配音→匹配素材→渲染）
- 跑完自动做成片体检（时长/画面/声音），结尾打 `VERIFY_PASS=n/m`
- 退出码：0 全过 / 1 出片失败（`FAILED_STAGE=` 指明挂在哪一步；报错对照 engine-reference.md，常见网络问题，Edge 配音要联网）/ 2 出片了但有成片没过体检 / 130 手动停

### 第 5 步：交付

- **硬门禁：`VERIFY_PASS=n/m` 不是 m/m 就不能说完成。** 没过的按 FAIL_REASONS 定位：黑帧 → 素材有问题，换素材重出；无声 → 配音丢了，重跑；时长不足 → 文案太短，回第 3 步；方向不对 → 检查 `--aspect` 参数。体检也可以单独重跑：`python scripts/verify_output.py --dir engine/output`
- 报成片绝对路径（`engine/output/` 下）+ 每条的合规检查结果（看成片清单 `===VIDEOS_START===` 块里的 FILE / STATUS / COMPLIANCE：STATUS=OK 本次新出、SKIP 续跑沿用）
- 合规未过的条目：指出是哪句文案触的词，改完重出
- 提醒一句：「发布前自己再过一遍画面和文案，投放内容的法律责任在使用者」
- 用户要继续出片 → 回第 3 步；换产品 → 第 2 步补素材

## 边界

- 引擎源码在 `engine/`（AdFlow v0.2 分享版，本地剪辑引擎）。Claude 不改引擎代码；调不动的问题看 engine-reference.md，再不行如实告诉用户卡在哪。
- 图形界面（`engine/main.py`）是可选的：用户想点点鼠标管素材也可以开，但 skill 流程全部走脚本，不依赖界面。
- 数字人、CLIP 智能混剪这类重型功能默认关闭，用户主动问再讲（要另装环境）。

## 免责声明

- 本 skill 按「现状」提供（MIT 许可），作者不对使用结果作任何保证。
- 使用者自负合规责任：请遵守你所在平台的服务条款与当地法规；生成的任何内容发布前请自查（广告法、违禁词、版权）。
- 本包不代任何第三方品牌、不含第三方私有数据；文中出现的第三方产品名仅为功能互操作说明或示例，与相应方无关联、无赞助。
- 你导入的素材、字体、音乐、配音的版权由你自负，商用前确认授权；成片发布前过一遍目标平台的审核规则。
