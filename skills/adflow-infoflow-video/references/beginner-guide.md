# 纯小白引导（从零开始）

你不需要看懂全部，卡在哪一节就看哪一节。实在不行，把报错截图发给 Claude，让它带你走。

## 1. 装 Python（电脑上没有 Python 时）

1. 打开 https://www.python.org/downloads/ ，点黄色的 **Download Python 3.12.x**
2. 双击下载的安装包，**最重要的一步**：第一个界面最下面勾上 **Add python.exe to PATH**，再点 Install Now
3. 装完验证：按 `Win + R`，输入 `cmd` 回车，黑窗口里输入 `python --version` 回车，显示 `Python 3.12.x` 就成功了
4. 显示「不是内部或外部命令」→ 没勾 Add to PATH，卸载重装一遍，记得勾

版本要 3.10 ~ 3.12（太新的版本可能装不上某些依赖）。

## 2. 怎么跑命令（所有「运行 xxx」都是这个意思）

1. 打开 skill 文件夹（有 SKILL.md 的那层）
2. 点一下上方的地址栏，输入 `cmd` 回车 —— 会弹出黑窗口，且已经站在这个文件夹里
3. 把要跑的命令粘贴进去（右键就是粘贴），回车

其实最省事的办法：直接在 Claude Code 里说「帮我检查环境」，Claude 会替你跑。

## 3. 装 ffmpeg（剪辑工具，缺了它出不了片）

最简单：`python scripts/setup_env.py --ffmpeg`

它会自动下载（约 80MB）并解压到 `engine/ffmpeg/`，装完自动检查。

下载太慢或失败时手动装：

1. 浏览器打开 https://www.gyan.dev/ffmpeg/builds/ ，下载 **ffmpeg-release-essentials.zip**
2. 解压后得到 `ffmpeg-x.x-essentials_build` 文件夹
3. 在 `engine/` 里新建文件夹改名 `ffmpeg`，把解压的东西整个放进去，保证 `engine/ffmpeg/` 下面能看到 `bin/ffmpeg.exe`
4. 跑 `python scripts/check_env.py`，显示 ffmpeg [OK] 就成了

## 4. 装 Python 依赖（第一次用时装一次）

`python scripts/setup_env.py --deps`

走清华镜像，几分钟。装完跑 check_env.py 复查。

## 5. 常见卡点

- **pip 下载慢/超时**：脚本默认已走清华镜像；还慢就换个网络再试
- **杀毒软件报警**：ffmpeg 和 Python 脚本不是病毒，选「允许」
- **命令里带路径要加英文双引号**：比如 `--dir "D:\我的素材"`，路径有空格、中文时必须加
- **窗口里中文变问号**：不影响功能，看 [OK] / [X] 就行
- **不小心关了黑窗口**：没大事，重新打开再跑一次命令

## 6. 文件都放在哪

- 你的视频素材 → `engine/materials/`
- 背景音乐（自己有授权的） → `engine/bgm_library/`
- 成片 → `engine/output/`
- 数据记录 → `engine/data/`
- 想彻底重来 → 删掉 `engine/data/adflow.db` 就清空了素材库（成片不受影响）
