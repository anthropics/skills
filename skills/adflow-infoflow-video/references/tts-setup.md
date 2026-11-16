# 配音配置教程（三选一）

默认已经用 **A 方案（免费）**，什么都不用做。想换更好的音色再看 B/C。

出片时想临时指定音色：`python scripts/make_videos.py --text-file 文案.txt --voice 音色名`

## A. 微软 Edge-TTS（默认，免费，推荐先用这个）

- 不用注册、不用 key、不限量（微软公网接口，稳定性一般，偶尔超时重跑即可）
- 常用音色（`--voice` 参数或改 `engine/config.yaml` 的 `tts.edge_tts.voice`）：

| 音色名 | 效果 |
|---|---|
| zh-CN-XiaoxiaoNeural | 女声，标准播音感（默认） |
| zh-CN-XiaoyiNeural | 女声，温柔年轻 |
| zh-CN-YunxiNeural | 男声，阳光青年 |
| zh-CN-YunyangNeural | 男声，新闻播音 |
| zh-CN-YunjianNeural | 男声，浑厚有力 |

- 出多条视频时引擎会自动男女声交替（想关：`config.yaml` → `tts.voice_diversity.enabled: false`）

## B. 火山引擎 TTS（付费，音质更像真人）

1. 打开 https://www.volcengine.com/ 注册并完成实名认证（个人可）
2. 控制台搜「语音技术」→ 开通 **语音合成大模型声音复刻/语音合成**（按字符计费，新用户一般有免费额度）
3. 在控制台拿到两个值：**App ID**（应用 ID）和 **Access Token**（访问令牌）
   - 拿令牌的位置一般在「语音技术 → API Key 管理」；建应用后看应用详情页
4. 用记事本打开（没有就新建）`engine/.env`，加两行（换成你自己的值）：
   ```
   VOLCANO_TTS_APP_ID=你的AppID
   VOLCANO_TTS_TOKEN=你的AccessToken
   ```
5. 改 `engine/config.yaml`：`tts:` 下面 `backend: edge` 改成 `backend: volcano`
6. 验证：`python scripts/check_env.py` → 显示「配音方案: 火山引擎（key 已配置）」

常用音色：BV001_streaming（通用女声，默认）、BV002_streaming（通用男声）、BV700_streaming（综艺女声）、BV701_streaming（综艺男声）。改 `config.yaml` → `tts.volcano.voice` 或出片时 `--voice BV002_streaming`。

## C. MiniMax TTS（付费，情感表现好）

1. 打开 https://www.minimaxi.com/ （MiniMax 开放平台）注册并实名
2. 控制台 → API Keys → 创建一个 key；账户信息里能看到 **Group ID**
3. `engine/.env` 加两行：
   ```
   MINIMAX_API_KEY=你的key
   MINIMAX_GROUP_ID=你的GroupID
   ```
4. `engine/config.yaml`：`backend: edge` 改成 `backend: minimax`
5. 验证：`python scripts/check_env.py` → 显示「配音方案: MiniMax（key 已配置）」

常用音色：Chinese_Warm_Woman（温柔女声，默认）、Chinese_Sweet_Girl、Chinese_Calm_Man。改 `config.yaml` → `tts.minimax.voice`。

## 换回免费方案

`engine/config.yaml` 里 `tts.backend` 改回 `edge` 即可，随时可换。

## 注意

- `.env` 里有 key，别把这个文件发给别人（正常分享 skill 包不含它）
- 付费方案按用量扣费，出片前脚本会打印预估成本
- 三种方案都可以用 `--rate` 调语速（0.9 慢 / 1.1 快），`--voice` 临时换单条音色
