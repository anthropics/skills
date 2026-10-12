---
name: weather-query
description: >
  查询中国任意城市或地区的天气信息，使用和风天气（QWeather）API。
  当用户提到天气、气温、下雨、预报、空气质量、今天天气怎么样、明天要带伞吗、
  某城市天气、某地区天气等相关问题时，必须使用本 Skill。
  支持实时天气、3天/7天预报、空气质量查询。
  哪怕用户只是顺带一提（如"北京今天冷不冷"、"上海明天会下雨吗"），也要触发本 Skill。
---

# 天气查询 Skill（和风天气）

本 Skill 帮助用户查询中国任意城市/地区的实时天气、天气预报和空气质量。
数据来源：[和风天气 QWeather](https://www.qweather.com)（免费注册可用）

---

## 首次安装：配置 API Key

本 Skill 需要用户自行配置和风天气的 API Key。**API Key 免费获取**，步骤如下：

1. 前往 [https://dev.qweather.com](https://dev.qweather.com) 注册免费账号
2. 登录后进入控制台，创建一个「应用」
3. 复制生成的 API Key

然后在终端运行一次配置命令（只需配置一次，永久生效）：

```bash
python <skill_dir>/scripts/get_weather.py --setup
```

按提示粘贴 API Key 即可。Key 会安全保存在本地 `~/.config/weather-query/config.json`，不会上传任何地方。

> 高级用法：也可以设置环境变量 `QWEATHER_API_KEY=你的Key` 来临时使用。

---

## 日常使用

配置好 API Key 后，直接用中文问天气即可触发本 Skill。

**脚本路径**：`<skill_dir>/scripts/get_weather.py`

### 基础命令

```bash
python <skill_dir>/scripts/get_weather.py <城市名称>
```

默认同时返回：实时天气 + 3天预报 + 空气质量

### 参数说明

| 参数 | 说明 | 示例 |
|------|------|------|
| `城市名称` | 必填，支持中文城市名 | 北京、成都、三亚、西藏拉萨 |
| `--type now` | 只看实时天气 | `--type now` |
| `--type 3d` | 只看3天预报 | `--type 3d` |
| `--type 7d` | 只看7天预报 | `--type 7d` |
| `--type all` | 全部信息（默认） | `--type all` |
| `--no-air` | 不查空气质量 | `--no-air` |

### 命令示例

```bash
python <skill_dir>/scripts/get_weather.py 北京
python <skill_dir>/scripts/get_weather.py 上海 --type now
python <skill_dir>/scripts/get_weather.py 成都 --type 7d
```

---

## 工作流程

1. **识别意图**：识别用户想查哪个城市、需要哪类天气信息
2. **检查配置**：如果脚本报错说缺少 API Key，先引导用户运行 `--setup`
3. **运行脚本**：用 Bash 工具执行查询命令
4. **解读结果**：将输出友好呈现，必要时加一句贴心建议

## 处理用户的不同问法

| 用户问法 | 建议命令 |
|---------|---------|
| "北京今天冷吗" | `--type now` |
| "明天上海会下雨吗" | `--type 3d` |
| "成都这周天气" | `--type 7d` |
| "广州空气好不好" | `--type now` |
| "三亚适合旅游吗" | `--type 7d` |

## 贴心建议（可选附加）

根据天气数据，可在结果后补充一句简短建议：
- 低于 10°C → 建议添衣
- 有降水 → 记得带伞
- 空气"差"或"极差" → 建议减少户外活动
- 紫外线强 → 提醒防晒

## 错误处理

| 错误信息 | 解决方式 |
|---------|---------|
| 未找到 API Key | 引导用户运行 `--setup` 配置 Key |
| API Key 无效 | 检查 Key 是否复制完整，或重新运行 `--setup` |
| 未找到城市 | 尝试更常见的城市写法（如"广州"而非"穗"） |
| 网络连接错误 | 检查网络，稍后重试 |
