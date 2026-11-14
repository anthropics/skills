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

## 二、卡点流水线（BGM 主时钟路径）

```
bgm.mp3
  → librosa 提真实鼓点 + 起音强度/响度             engine/beat_cutter.py extract_beat_map
  → 按小节能量分段定切点密度（高潮每拍/平稳两拍/四拍） plan_cuts
  → 素材按节奏取窗口（运动打分优选，短料慢放补齐）    engine/shot_picker.py + make_beat_video.py
  → 踩点特效（punch缩放/白闪/镜像/倒放/抖动/大字快闪） engine/beat_effects.py
  → ffmpeg 渲染 + 响度归一                           engine/output/beat_*.mp4(+.cuts.json)
```

- 和文案路径的区别：没有配音没有字幕渲染没有合规检查（自用向）；BGM 音量 0.9（文案路径 0.15）
- 切点表 `.cuts.json` 与成片同名落在一起（含 accent/reverse/shake 标记和每镜素材来源），验刀/复现看它

### make_beat_video.py 参数

| 参数 | 默认 | 说明 |
|---|---|---|
| --bgm | 必填 | BGM 文件（用户自有授权） |
| --style | flash | flash 每拍一刀 / standard 两拍一刀 / build 前缓后炸 |
| --duration | 0=整首 | 成片秒数，60 秒封顶（config beat_cut.max_duration） |
| --words | 空 | 大字快闪词，空格/逗号分隔，最多 24 个 |
| --count | 1 | 出几条（素材顺序/窗口不同） |
| --aspect | portrait | 竖屏/横屏 |
| --bgm-volume | config 0.9 | BGM 音量 0~1 |
| --reverse | config 0.15 | 倒放镜头占比 0~1（0=不倒放） |
| --seed | 0 | 固定种子 = 可复现同一条 |
| --force | 关 | 已出的成品也全部重出（默认同参数重跑跳过已出条目只补缺） |

### 输出协议（跑完看什么）

- 成片清单标记块：`===VIDEOS_START===` 里逐条 `FILE=` + `STATUS=OK|SKIP|FAIL`（SKIP=断点续跑沿用旧成片；FAIL 带 `FAILED_STAGE=` 拼镜头/渲染/响度归一/写切点表，指明挂在哪一步）
- 跑完自动成片体检（verify_output.py 同款检查），结尾 `VERIFY_PASS=n/m`
- 退出码：0 全过 / 1 一条没出（素材全挂或没节拍）/ 2 有条目失败或没过体检 / 130 手动停
- 体检单独重跑：`python scripts/verify_output.py --dir engine/output`（详细判定项见该文件头注释）

### 断点续跑与缓存（怎么少干重复活）

- **续跑判据**：每条成片的参数指纹写在其 `.cuts.json` 的 `sig` 字段（CLI 参数 + BGM 文件身份 + 种子）。重跑同命令时已出且 sig 一致的条目直接跳过；中途挂的条目会清掉半截文件，重跑只补缺的
- 改了 CLI 参数自动视为新条目；改了 config 效果预设 sig 不变，要全部重出加 `--force`
- **归一化缓存**：素材预处理（缩放裁剪到目标分辨率）结果落 `engine/cache/normalize/`，跨次出片复用不重编码。缓存键含文件路径+大小+mtime——同路径换了文件（重新导过素材）会自动重新归一化，不会吃旧缓存；`.part.mp4` 是中断残留，10 分钟后自动清
- 换横竖屏 = 分辨率进缓存键，两套缓存互不干扰

## 三、make_videos.py 参数

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

## 四、素材库与标签

- 库：`engine/data/adflow.db`（SQLite）。清空重导 = 删这文件
- 打标 15 维度的枚举值以 `scripts/apply_tags.py` 文件头注释为准（与引擎 Vision 打标同构）
- 匹配优先用 scene/shot_type/product_visibility 等结构化标签 + free_tags；未打标素材也能被匹配（兜底全库），但画面相关性差
- 竖屏出片只用竖素材（h≥w 即算竖），竖素材不足自动放行高清横素材裁切

## 五、config.yaml 常动开关

skill 版已调好的默认（不用动）：`tts.backend: edge`、`segmentation.enabled: false`（标点断句）、`diversity.match_weights.semantic: 0`（免装 CLIP）、`digital_human.enabled: false`。

| 键 | 作用 |
|---|---|
| tts.backend | edge（免费）/ volcano / minimax |
| tts.speech_rate | 全局语速（默认 1.1） |
| editing.default_resolution | 输出分辨率（默认 1080x1920） |
| editing.subtitle.font_size | 字幕字号（默认 56） |
| editing.subtitle.cta_color | 结尾 CTA 句字幕色（默认 white；改红色 #FF4444 在红/暖色素材上会看不见） |
| editing.shot_duration_ms | 每镜默认时长（默认 2500） |
| beat_cut.style_presets.* | 卡点三风格的效果参数（punch 幅度/flash 颜色/mirror_every 镜像间隔/calm_zoom 缓推） |
| beat_cut.word.* | 大字快闪字号/颜色/描边 |
| beat_cut.bgm_volume / max_duration | 卡点片 BGM 音量（0.9）/ 时长封顶（60s） |
| beat_cut.motion_pick / reverse_ratio / shake_every | 运动打分选镜头开关 / 倒放占比（0.15）/ 每 N 个重音刀换抖动（4，0=关） |
| bgm.enabled | 是否自动配乐（默认 true，空库等于没配乐；只管文案路径，卡点路径必带 BGM） |
| compliance.check_ad_law | 广告法检查开关（保持 true） |

## 六、常见报错对照

| 报错/现象 | 原因 → 处理 |
|---|---|
| `ffmpeg not found` / 渲染段空 | 没装 ffmpeg → `python setup_env.py --ffmpeg` |
| `No module named xxx` | 依赖没装全 → `python setup_env.py --deps` |
| edge-tts 超时 / `NoAudioReceived` | 微软接口网络抖动 → 重跑一次；连发多条失败换网络或考虑付费方案 |
| 配音 401/403 | 付费方案 key 错/过期 → 对照 tts-setup.md 重配 |
| `素材库是空的` | 没导素材 → import_materials.py |
| 成片画面重复多 | 素材太少（<3 条）或太短（<2s 降权）→ 补素材 |
| 合规检查未过 | 文案触禁语（输出会指明词）→ 改词重出 |
| 渲染卡在 0% 很久 | 正常，TTS 和渲染按条进行，一条几分钟 |
| moviepy 内存报错 | 单条素材过大（>500MB）→ 切小再导 |
| 卡点：`测不出节拍` / `没检测出节拍` | 音乐节奏不清晰或近乎无声 → 换鼓点强的歌，不是故障 |
| 卡点：`成片时长内只有 N 拍` | --duration 给太短或歌太慢 → 加时长或换歌 |
| 卡点：成片镜头重复感强 | 素材少（<5 条）或素材太短 → 补素材 |
| 卡点：`素材加载失败，跳过 xxx` | 单条素材坏了（文件损坏/编码不支持）→ 引擎自动跳过用其余素材，有余量就不用管；这条素材换好版重导即可 |
| 卡点：退出码 2 / STATUS=FAIL | 看 FAILED_STAGE 挂在哪步；重跑同命令只补失败条目 |

## 七、目录

```
engine/
  adflow/            引擎源码（agents/engine/db/gui/compliance/...）
  main.py            可选图形界面（python main.py）
  config.yaml        全局配置
  .env               付费配音 key（用户自建，不随包分发）
  materials/         视频素材库
  bgm_library/       背景 Music（用户自有授权）
  data/              数据库+关键帧
  cache/normalize/   素材归一化缓存（跨次复用，删掉=下次重编码）
  output/            成片（含 _filter_reports 合规报告）
```
