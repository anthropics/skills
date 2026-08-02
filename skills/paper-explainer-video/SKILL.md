---
name: paper-explainer-video
description: 把一篇论文做成中文科普短视频(Manim 动画 + edge-tts 中文配音 + 合成BGM + Live2D 二次元虚拟主播念稿)。当用户说"把这篇论文做成科普视频/讲解视频""用 manim 讲这篇 paper""加配音/加二次元主播/Live2D 念稿"等时使用。
---

# 论文 → 科普短视频 流水线

把一篇论文做成 3-5 分钟中文科普视频。产物：
- Manim 渲染的分场景动画(1080p60)
- edge-tts 中文配音(逐句对齐画面节拍)
- 自制免版权 BGM(合成的 ambient pad)
- 右下角 Live2D 二次元虚拟主播，口型由配音音量实时驱动
- 自动加交叉转场、片头"论文精读"开场、片尾参考文献

`assets/` 里是**通用脚本**(基本不用改)，每篇论文只需重写 3 个文件：
`scenes.py`(动画)、`narration_data.py`(旁白)、`pipeline_config.py`(场景列表/片名/嗓音)。

---

## ⚠️ 三条铁律(踩过的坑，务必遵守)

1. **永远用非 iCloud 的本地 venv 渲染**。若项目在 iCloud 同步的桌面/文稿目录，
   `.venv` 会被 iCloud 反复驱逐，导致渲染在 import 时随机卡死/超时(Errno 60)。
   统一用 `~/llm_mc_venv`(setup.sh 会建好)。
2. **重活在 `/tmp` 本地目录跑，只把成片拷回项目**。渲染/合成读写都走 `/tmp/paper_build`，
   避免 iCloud 卡顿；最后 `cp` 成片回项目。
3. **先看磁盘**。`df -h /tmp`。Live2D 原始帧很占空间——本流水线已改为把角色的
   **原始 RGBA 帧直接管道进 ffmpeg 合成**，不落大中间文件(既保证透明，又省磁盘)。
   不要再用 qtrle/.mov 存整段 avatar(800MB+)。

---

## 一次性环境准备

```bash
bash ./assets/setup.sh
```
它会：建 `~/llm_mc_venv` → 装 manim / edge-tts / live2d-py / glfw / PyOpenGL / numpy / scipy / pillow
→ 浅克隆 live2d-py 取免费样例模型到 `/tmp/live2dpy`(含 llny / Mao / Haru)。
还需要系统已装 `ffmpeg`、`ffprobe`(`brew install ffmpeg`)。中文字体用 macOS 自带 PingFang SC。

---

## 每篇论文的工作流

设新项目目录为 `$PROJ`(放论文、产出成片)，本地工作区 `MC=/tmp/paper_build`。

### 0) 拷贝通用脚本到项目
```bash
cp ./assets/{make_bgm,narrate,build_video,render_avatar,pipeline_config,narration_data,scene_helpers}.py "$PROJ"/
cp ./assets/status.sh "$PROJ"/
```

### 1) 读论文，设计 5-8 个场景
读 `$PROJ` 里的论文(txt/pdf)。设计场景序列，典型结构：
1. `IntroScene` — 片头"论文精读"：论文标题/作者/arXiv +「今天我们一起来精读这篇论文」
2. `HookScene` — 钩子：一个让人想看下去的问题/反直觉现象
3-6. 核心机制场景 — 每个讲一个 intuition，配 Manim 动画(曲线/直方图/分布演化/对比)
7. `ConclusionScene` — 结论 + 钩子化金句
8. `ReferencesScene` — 片尾参考文献(作者、标题、arXiv)

原则(见 reference/ 里的范例)：
- 不堆数学，一个场景讲一个直觉；每个动画 ≤ 15 秒，5 分钟内不冷场。
- **随机过程一律用固定种子预计算**(放 `model_collapse_data.py` 之类的数据模块)，
  scene 里绝不跑随机数 → 每次渲染一致、可迭代。
- 中文用 `Text(..., font="PingFang SC")`；颜色高亮、半透明 trace 留旧曲线。
- ⚡ **变化的数值/标签千万别用 `MathTex`**：它每次都起 `latex` 子进程，极慢——实测
  GaussianCollapse 里逐代刷新 μ/σ 的 MathTex 让该场景从 75s 涨到 183s(占一半)。
  逐代/逐帧变的数用 `Text`(`μ σ Σ √` 等直接打 unicode)或 `DecimalNumber`(可动画)。
- ⚡ **静态公式千万别用 `Text`/`cn()` 排数学**：`m_t` 的下标 `_t` 会**原样显示**，
  `ᵗ`/`θₜ`/`m̂` 这类 unicode 上下标/hat 在 PingFang SC 里**可能缺字成豆腐块**，非常掉价。
  **所有静态公式一律 `MathTex(r"...", color=...)` 走真 LaTeX**(且要 `export PATH` 带上 latex，
  否则静默失败)。唯一例外是"逐帧变化的数值"(见上一条)。实测 12 场景 ~12 个静态公式
  全部 MathTex 只增加几十秒渲染，代价可忽略。
- 兼容提示: manim 0.20 不导出 `HGroup`, 并排用 `VGroup(a, b).arrange(RIGHT, buff=0.15)`。
- 论文里的原始文本/图(如 LLM 输出样例、关键图)直接引用并标注出处。

### 2) 先写 narration_data.py + pipeline_config.py(**暂不写 scenes.py**)
- `narration_data.py`：`NARRATION = [[...每个场景的句子...], ...]`(顺序与 SCENES 对齐)；
  `SCENE_RATES = {i: "+12%"}` 给偏长的场景单独加速。
- `pipeline_config.py`：`SCENES`(场景类名顺序)、`OUTPUT_BASENAME`、`VOICE`/`PITCH`、
  `AVATAR`(主播构图/位置)、`L2D_MODEL`、`USE_AVATAR`。

### 2.5) ★ 先跑 TTS 拿到每段配音真实时长(关键!省一次全量重渲)
**别拍脑袋定 `self.wait()`**。实测教训:写完 scenes 渲完才发现配音比画面长 → 改 17 处 wait → 重渲全部 = 白白多花 5-7 分钟。正确顺序:先生成配音,拿到时长,再据此写场景。
```bash
cd "$MC" && $V narrate.py 2>&1 | grep -E "scene[0-9]"
# 输出形如:  scene0  20.6s  108字 / scene1  28.4s  136字 / ...
```
记下这 N 个时长。

### 2.6) 再写 scenes.py(按配音时长定 wait + 右下角避让主播)
- 每个 `construct` 的 **(所有 run_time + 所有 wait) 之和 ≥ 该场景配音时长 + ~1.5s 缓冲**，一次写对。
- ★ 更稳的写法(实测帧级精确): 场景末尾调一个 `finish()` 助手, 用 `self.renderer.time`
  读出已消耗时间, 把剩余量精确 `wait()` 掉再统一淡出 → 场景时长**严格等于目标值**, 不用手数
  `run_time+wait` 也能保证 ≥ 配音+缓冲:
  ```python
  def finish(scene):
      remain = TARGET[type(scene).__name__] - scene.renderer.time - 1.2
      if remain > 0: scene.wait(remain)
      if scene.mobjects: scene.play(*[FadeOut(m) for m in scene.mobjects], run_time=1.2)
  ```
  (TARGET = 各场景配音时长 + 1.8s。manim 会把每个动画时长按帧量化, 但 `renderer.time`
  反映量化后真实值, 末尾 wait 会吸收全部累积误差。)
- **右下角是主播区**(若 `USE_AVATAR`)。把关键内容(曲线尾部、读数、字幕)放在别处；
  迭代时开 `SHOW_AVATAR_ZONE=1` 让每幕画出红色避让框(见 `assets/scene_helpers.py`):
  ```python
  from scene_helpers import cn, add_avatar_guard   # cn=中文Text; guard=主播红框(调试)
  class FooScene(Scene):
      def construct(self):
          add_avatar_guard(self)   # SHOW_AVATAR_ZONE=1 时显示主播占位红框, 出片自动隐藏
          ...
  ```
  这样写动画时就知道避开右下角 → 避免 Live2D 渲完才发现遮挡、再重渲(省 3-5 分钟)。
- Manim 场景类参考 `reference/scenes_example.py`。

### 3) 渲染分场景(本地 venv，并行 + 开缓存 + 两档质量)
```bash
MC=/tmp/paper_build; V=~/llm_mc_venv/bin/python
export PATH="/Library/TeX/texbin:$PATH"   # ★ 必须! MathTex 场景需要 latex 在 PATH, 否则静默失败
rm -rf "$MC"; mkdir -p "$MC"; cp "$PROJ"/{scenes,pipeline_config,narration_data,make_bgm,narrate,build_video,render_avatar,scene_helpers}.py "$MC"/ 2>/dev/null
cp "$PROJ"/<数据模块>.py "$MC"/ 2>/dev/null
cd "$MC"

# 迭代阶段: 低质量(-ql 480p15, 约比 -qh 快 ~16x), 并行 4 路。改了排版/时长就重跑。
SCENES=$($V -c "import pipeline_config as c;print(' '.join(c.SCENES))")
Q=1080p60   # 迭代时改成 ql 对应的目录名也行; 这里演示成片档
render() { # 用法: render <质量flag> <质量目录>
  printf '%s\n' $SCENES | xargs -P 4 -I{} bash -c '
    S={}; for a in 1 2 3; do
      [ -f media/videos/scenes/'"$2"'/$S.mp4 ] && exit 0
      '"$V"' -m manim '"$1"' --media_dir "'"$MC"'/media" scenes.py $S >/tmp/r_$S.log 2>&1
      [ -f media/videos/scenes/'"$2"'/$S.mp4 ] && exit 0
    done; echo "FAILED $S; tail /tmp/r_$S.log"'
}
render -ql 480p15      # 迭代: 快, 抽帧查排版/出界/坐标轴裁切都看得出
# 定稿后再出高质量:
render -qh 1080p60
```
说明:
- **不再用 `--disable_caching`** —— 那条只为躲 iCloud, 但工作区在 `/tmp`(iCloud 不碰),
  开缓存后没改的 `play()` 块复用 partial movie file, 迭代快几倍。
  改了**数据模块**后清一次缓存: `rm -rf "$MC"/media/{Tex,texts}` 或加 `--flush_cache` 跑一遍。
- ⚠️ **改过 `scenes.py` 后重渲, 务必先清该质量档缓存**: `rm -rf "$MC"/media/videos/scenes/<质量档>`
  (如 `480p15`/`1080p60`)。否则残留的 partial movie 会把场景时长**虚增 1~2s**
  (实测 ProblemScene 被撑到 67.07s, 目标 65.5s), 直接破坏第 2.5 步建立起的配音同步。
  自检: 渲染后 `ffprobe` 每段时长应 ≈ TARGET(配音时长+1.8s), 偏差 >0.1s 即缓存污染,
  用 `--disable_caching` 重渲验证。
- **并行 `-P 4`**(场景互相独立)。内存紧/缓存写冲突就降到 `-P 2`。
- **两档质量**: 95% 时间在迭代构图/时长, 用 `-ql`; 只在定稿/对配音时切 `-qh`(或 `-qm` 720p 折中)。
- 抽帧自检见步骤 8(低质量帧也能看出排版问题)。

### 4) 配音(已在 2.5 生成) + 复核
配音在步骤 2.5 已生成。这里只需复核:**每段配音 ≤ 对应场景画面时长**(你在 2.6 已按时长定 wait,应当满足)。
只有当你**改了 `narration_data.py`** 才需重跑 `cd "$MC" && $V narrate.py`(并行、~10s)。
> BGM(步骤 5)与渲染无依赖, 可在 step 3 渲染时后台并行: `$V make_bgm.py 240 bgm.wav &` … `wait`。

### 5) BGM
```bash
$V make_bgm.py <总秒数±余量> bgm.wav   # 例: 240
```

### 6) 合成底片(转场 + 配音 + BGM)
```bash
/opt/homebrew/bin/python3 build_video.py 1080p60 bgm.wav   # build_video 只用标准库
mv -f "$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_1080p60.mp4" base_video.mp4
```
> 迭代预览想更快: `MC_FAST=1 python3 build_video.py ...`(走 h264_videotoolbox 硬编, 快 5-10x; 定稿去掉)。

### 7) Live2D 虚拟主播 → 直接合成成片(`USE_AVATAR=True` 时)
```bash
$V render_avatar.py     # 读 base_video.mp4 时间轴对齐口型；原始RGBA管道直出成片(无大中间文件)
cp "$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_live2d.mp4" "$PROJ"/
cp base_video.mp4 "$PROJ/$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_1080p60.mp4"
```
> 同样支持 `MC_FAST=1 $V render_avatar.py` 走硬编预览。
> **`USE_AVATAR=False`(FAST 模式)**: 跳过这步, 成片就是 `base_video.mp4`, 省 3-5 分钟。

### 8) 抽帧自检(必做)
每改一次都抽帧看，别凭感觉：
```bash
ffmpeg -y -ss <秒> -i 成片.mp4 -frames:v 1 /tmp/chk.png      # 整帧
ffmpeg -y -ss <秒> -i 成片.mp4 -filter_complex "crop=400:300:1380:780,scale=520:-1" -frames:v 1 /tmp/zoom.png  # 放大看主播
```
用 Read 看 png。重点查：① 主播**整张脸**在框内(不是半张)；② 主播背景**透明**(不是黑框)；
③ 静音处主播**闭嘴**(证明口型真同步)；④ 字幕/曲线没被主播挡住。

进度随时看：`bash status.sh`(或 `-w` 滚动)。

---

## Live2D 主播：关键参数与排错(reference/AVATAR_NOTES 同款)

主播参数在 `pipeline_config.AVATAR`：
- `scale` / `offset_x` / `offset_y`：摄像机。**模型默认脸偏右，必须用 offset_x 把脸居中**，
  否则摆头时脸的右半会被画框切掉 → 经典"半张脸"。当前 llny：`scale 1.55, offset_x -0.3, offset_y -1.55, W 460, H 470`。
- 调构图的标准动作：写个小脚本，对一组 (scale, offset_x, offset_y) 各渲一帧、拼成 grid、Read 看图选。
  **务必在施加最大摆头(ParamAngleX=8)时测**，确认极端姿势也不切脸。
- `crop`：取上百分比，裁掉胸口/底部(很多免费样例模型材质上有"免费"水印，裁掉即可)。
  注意别裁到下巴——下巴和水印高度接近时，宁可 crop 浅一点+接受极淡残留。
- `crop_left`：裁掉**左侧**百分比。⚠️ llny 在脸的**左侧**还有一处材质水印(汉字)，
  纵向 `crop` 根本裁不掉，必用横向裁。overlay 是右对齐的，所以裁左侧**不改变脸的位置和大小**。
  测法：抽一帧、按主播显示框裁出来(`crop=disp_w:disp_h:x:y`)，统计每列非黑像素找出
  "水印段 / 空隙 / 脸"三段 → llny 实测水印占 10.7%-29.3%、脸从 40.3% 起 → 取 0.35。
  换模型必须重测(默认 0.0 = 不裁)。
- `disp_w` / `margin_x` / `margin_y`：角落显示宽度与边距(margin_x 大=更靠左)。
- 摆头幅度别太大(ParamAngleX≈4)，否则容易摆出画框。
- 换模型：改 `L2D_MODEL` 指到 `/tmp/live2dpy/Resources/v3/<名>/<名>.model3.json`(Mao/Haru/llny)。

**透明**：必须走"原始 RGBA 帧管道直入 ffmpeg overlay"(render_avatar 已实现)。
不要用 VP9(alpha 易丢→黑框)，也不要用 qtrle 存大文件(爆磁盘)。

**嗓音**：`pipeline_config.VOICE`。可选(edge-tts zh-CN)：
`zh-CN-XiaoyiNeural`(卡通/活泼，最接近萝莉) `zh-CN-XiaoxiaoNeural`(温暖女声)
`zh-CN-YunyangNeural`(纪录片男声) `zh-CN-YunxiNeural`(年轻男声)。
`PITCH="+20Hz"` 可把声音调高更萌。真·GalGame 萝莉音需本地 GPT-SoVITS/Bert-VITS2(重，本机一般不上)。

---

## 性能 / 加速速查(已在本机实测, M系 8核/4性能核, 8场景 1080p60)

⚠️ **理论估计常常落空, 这些是真实测的数:**
| 做法 | 耗时 | 相对串行-qh |
|---|---|---|
| 串行 `-qh` 无缓存(旧基准) | 429s | 1.0x |
| **并行 `-P4` `-qh`** | 411s | **1.0x(没用!)** |
| **`-ql` 串行(迭代档)** | 216s | **2.0x** |
| **缓存命中重渲 `-qh`** | 120s | **3.6x ← 迭代最大杠杆** |

**单场景实测(无缓存 -qh):** GaussianCollapse 183s、GMMMerge 91s、LLMTextScene 83s、
TailCutoff 63s、HookScene 50s、其余 ~12-19s。长尾极不均(最重的一个占 1/3)。
→ **把最重场景里的 `MathTex` 换成 `Text`/`DecimalNumber`: GaussianCollapse 183s→75s(2.4x, 省108s)**,
比并行/降质都狠, 且对成片也生效。这是真正该花力气的地方, **不是拆场景**(本机并行无收益,
且 manim 已按 `play()` 缓存, 拆类不增加缓存粒度)。

**结论(诚实版):**
- **真正有用 = 缓存 + `-ql` 迭代 + 热点场景去 MathTex。** 前两者叠起来一轮迭代从 ~7min 降到 ~1-2min。
- **并行在这台机器没收益**: 单个 manim 已吃满 4 个性能核, 4 路并行只是互相抢核(xargs -P 本身确实在并行)。
  核更多的机器才有用。`-P 2` 无害, 不必强求。
- **真瓶颈是 manim 的矢量+Tex+动画建立开销**(与分辨率基本无关、也不并行), 不是像素填充——
  所以降分辨率只省一半, 并行不省。
- **配音/BGM 与渲染并行起**(`&`+`wait`)、**配音内部并行**(ThreadPoolExecutor): 省那几十秒串行。
- `MC_FAST=1`(videotoolbox 硬编)只影响 ffmpeg 合成段, 没在此基准里量化, 但硬编确实快很多。
- Live2D 渲染: 回读画框砍到 ~1.04x 显示尺寸(W/H 312/319, 原 380/388)+ 删冗余 `glFinish()` + **主播帧率 30→15fps**(`AVATAR.fps`)。
  主播是整条流水线第二大开销(~3-5min); fps 减半≈回读减半, 二次元"一拍二"本就 12fps, 15fps 反而更对味, 成片肉眼无差。
  口型包络/眨眼都按 `A["fps"]` 自动跟随, 只改 config 一处即可。**换 TTS 对速度无收益(配音才 ~10s 且已并行); 流式输出帮不上(主播必须等整条 base_video 对口型)。**

可选(没实测, 需要时再上): #7 合并两次编码(~1.3x, 破坏 build_video 独立性)、PBO 异步回读(~1.5-2x avatar, 有风险)。

**档位选择**: 日常迭代 = `-ql` + 开缓存(改数据模块后清 `media/{Tex,texts}`)；交付 = `-qh`。

## 两档模式: 发布 vs 自己快速看

真正吃时间的不是计算, 是**"渲染→发现问题→重渲"循环**。实测一篇 ~32min 里, 两次"事后才发现"
(配音对不上、主播遮挡)各逼出一次完整 -qh+Live2D 重渲(共 ~10min)。本 skill 的 2.5/2.6 步
(先 TTS 定 wait、写场景时画主播避让框)就是把这两个发现**提前到设计阶段**, 一次做对。

- **发布档(默认)**: `USE_AVATAR=True`、定稿 `-qh`、抽帧自检。同难度论文预计 ~22-28min(比不优化省~10min)。
- **FAST 自看档**: `USE_AVATAR=False` + 全程只 `-ql` + 少抽帧。预计 ~10-15min。用质量换速度,
  只适合自己快速过一篇; 要发出去/给人看就别开。
  开法: 改 `pipeline_config.USE_AVATAR=False`, 渲染用 `render -ql`, 合成 `MC_FAST=1`。

## 范例
`reference/scenes_example.py`(已用 `Text` 代替逐代 MathTex)、`reference/data_module_example.py`、
`reference/旁白_example.md` 是"模型崩溃"那篇做好的完整版，照着改最快。
