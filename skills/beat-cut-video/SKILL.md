---
name: beat-cut-video
description: 丢一首歌加素材，自动踩着鼓点剪卡点视频：重音配最炸画面、快闪大字、倒放混切全自动，几分钟出片。不用学剪辑软件。歌得节奏强，抒情的切不出卡点感。触发词：卡点视频、快闪视频、踩点混剪、BGM卡点、节奏出片。
display_name: 丢首歌自动剪卡点视频
display_name_en: Beat-Sync Video Cutter
description_zh: 丢一首歌和素材，自动踩鼓点剪卡点视频：重音配炸画面、快闪大字、倒放混切全自动。
description_en: Auto-cut beat-synced flash videos from your music and clips.
examples_zh:
- "用这首歌剪一条快闪卡点视频"
- "帮我做个 15 秒产品快闪"
- "把旅行素材踩着鼓点混剪"
examples_en:
- "Cut a flash video to this song"
- "Make a 15s product flash"
- "Beat-sync my travel clips"
version: 1.3.4
author: "ayan"
---

# 卡点/快闪节奏出片（beat-cut）

你（Claude）在这个 skill 里的角色：**版权把关 + 风格顾问**。BGM 和素材的版权问话、帮用户挑风格是你的活；节拍提取、切点规划、特效渲染全部交给本地引擎脚本跑。**任何一步都不需要调外部大模型 API。**

和文案出片（adflow-infoflow-video，另一个 skill）的区别：那边配音是主时钟，2-3 秒一个镜头讲卖点，是广告向；这边 BGM 是主时钟，鼓点在哪刀落在哪，快的时候 0.5 秒一切，自然流量卡点风，全程无配音无口播——给 BGM 和素材就能出片。素材导入流程两边一样，素材库各自独立。

## 硬性红线（每次开工前自查，违反就停）

1. **BGM 版权（第一红线）**：BGM 是这条流水线的主角，版权问题比哪都大。只允许用户自己创作或拿到使用授权的音乐。绝不给用户找下载链接、不推荐盗版音乐源。用户说不清来源 → 先讲清风险，用户明确确认有授权才开工。
2. **素材版权**：动手导入素材前必须问一句「这些视频素材都是你自己拍的，或者拿到了使用授权吗？」用户否认或含糊 → 拒绝用这批素材出片。
3. **不碰别人成果**：不下载、不扒别人的视频当素材；看到别人的卡点视频好看，复制的是风格和节奏，不是画面。

## 工作流程

按顺序走，每一步做完确认没问题再进下一步。用户是纯小白时，把你要做的事用一句话说清楚再动手。

### 第 0 步：解压引擎 + 环境体检（首次必做）

先解压引擎（`engine/adflow/` 已存在就跳过）：Windows PowerShell 跑 `Expand-Archive engine/adflow-engine.zip engine/ -Force`；Mac/Linux 跑 `unzip engine/adflow-engine.zip -d engine/`。然后体检：

```bash
python scripts/check_env.py
```

- 全 [OK] → 跳到第 1 步
- 有 [X] → 按输出里的「怎么修」处理：缺依赖/缺 ffmpeg 跑 `python scripts/setup_env.py --all`（装依赖走清华镜像，ffmpeg 约 80MB）
- 用户电脑连 Python 都没有 → 打开 [references/beginner-guide.md](references/beginner-guide.md)，照「装 Python」一节带用户装
- 报错看不懂 → 对照 [references/engine-reference.md](references/engine-reference.md) 的「常见报错」解释

### 第 1 步：导入素材（首次必做）

先过红线 2（素材版权问话），然后：

```bash
python scripts/import_materials.py --dir "用户的素材文件夹"
```

导完就能出片——引擎按画面运动强度自动选镜头（重音刀配动得最狠的画面），不依赖标签。想精挑画面顺序再看图打标签（可选加分项）：

1. 读 `engine/data/keyframes/manifest.json`
2. 用 Read 工具逐条看关键帧图片（`data/keyframes/<素材ID>/f1.jpg` ~ `f4.jpg`）
3. 按 [scripts/apply_tags.py](scripts/apply_tags.py) 文件头注释里的维度写标签，写进 `engine/data/keyframes/tags.json`
4. `python scripts/apply_tags.py`

卡点很吃素材量：快闪 15 秒要切 25~30 个镜头，素材少于 5 条画面会重复，提前提醒用户多备些。

### 第 2 步：BGM（必做，先过版权）

过红线 1（BGM 版权问话），让用户把音乐文件放进 `engine/bgm_library/` 或直接给路径。

拿到先替用户把关一次：

- 报一下时长和大概的快慢（引擎出片时会打 BPM）
- 抒情慢歌/纯钢琴这类没有清晰鼓点的，直说「这种切不出卡点感，建议换节奏强的」，别让用户等半天出一条不满意的

### 第 3 步：选风格 + 快闪词（你给建议，别甩选择题）

| 用户想要 | 给这个 | 效果 |
|---|---|---|
| 炫酷快闪、产品快闪、转粉视频 | `flash`（默认） | 全程每拍一刀（约 0.5s 一切）+ punch 缩放 + 白闪 + 隔刀镜像 |
| 旅行 vlog、记录向、口播垫画面 | `standard` | 平稳段两拍一刀缓推，高潮段每拍一刀 |
| 前面铺垫后面炸、有情绪递进 | `build` | 前段四拍一刀慢慢推，进高潮（自动找 drop）全特效 |

快闪词（`--words`）：大字踩着鼓点弹出，如"夏天 旅行 自由"。3~10 个词最好，每词 1~4 字。

### 第 4 步：出片

```bash
python scripts/make_beat_video.py --bgm "engine/bgm_library/音乐.mp3" --style flash --words "夏天 旅行 自由"
```

- 常用参数：`--duration` 秒数（默认整首，60 秒封顶）、`--count` 出多条、`--aspect landscape` 横屏、`--reverse` 倒放镜头占比（默认 0.15，0=关）、`--seed` 固定随机种子复现同一条
- 引擎流程：提节拍 → 按段落定切点密度（切点锁 30fps 帧网格）→ 运动打分选镜头 → 倒放/抖动混切 + 踩点特效渲染，几分钟
- **断点续跑**：出片中断（死机/手动停）后重跑同一条命令，已出且参数一致的条目自动跳过，只补缺的和失败的；改了参数（或 config 效果预设）想全部重出加 `--force`
- 失败对照 [references/engine-reference.md](references/engine-reference.md) 排查；「测不出节拍」= 这首音乐节奏不清晰，换歌，不是故障

跑完看什么（机器可读标记块，别从散文里猜）：

- `===VIDEOS_START===` 逐条 `FILE=` + `STATUS=OK|SKIP|FAIL`（SKIP=续跑沿用旧成片；FAIL 带 `FAILED_STAGE=` 挂在哪一步）+ `VERIFY_PASS=n/m`
- 退出码：`0` 全过 / `1` 一条都没出 / `2` 有条目失败或没过体检（补跑同命令即可，别从头来）/ `130` 手动停

### 第 5 步：交付

- 报成片绝对路径（`engine/output/` 下）+ BPM、镜头数、高潮段起点（控制台都打了）
- **`VERIFY_PASS=n/m` 不是 m/m 就不能说完成**：按 FAIL_REASONS 对照处理——黑帧→素材坏换素材；无声→BGM 轨丢了重出；时长不足→`--duration` 给的太短；方向不对→查 `--aspect`。跳过的旧条目没过体检的话，加 `--force` 重出
- 同名 `.cuts.json` 是切点表：用户想核对某刀切在哪一秒，看这个文件
- 提醒一句：「发布前自己再过一遍画面；音乐和素材的版权责任在使用者」

## 边界

- 引擎源码在 `engine/`（本地剪辑引擎）。Claude 不改引擎代码；调不动的问题看 engine-reference.md，再不行如实告诉用户卡在哪。
- 这条流水线没有配音/口播（那是 adflow-infoflow-video skill 的活），BGM 是唯一声音。
- 图形界面（`engine/main.py`）不覆盖卡点流程，本 skill 全部走脚本。

## 免责声明

- 本 skill 按「现状」提供（MIT 许可），作者不对使用结果作任何保证。
- 使用者自负合规责任：请遵守你所在平台的服务条款与当地法规；生成的任何内容发布前请自查（广告法、违禁词、版权）。
- 本包不代任何第三方品牌、不含第三方私有数据；文中出现的第三方产品名仅为功能互操作说明或示例，与相应方无关联、无赞助。
- 你导入的素材、字体、音乐、配音的版权由你自负，商用前确认授权；成片发布前过一遍目标平台的审核规则。
