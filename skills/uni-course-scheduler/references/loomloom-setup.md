# LoomLoom 云端执行指南（买家侧）

## LoomLoom 是什么？

LoomLoom 是批量 LLM 云端执行平台，把结构化任务并行跑在固定管道里，
返回结构化结果。本 Skill 的「云端标准模式」通过 LoomLoom 市场执行。

本 Skill 支持**两个云端平台**，按你的支付方式选择（详见下方"选哪个平台"）：

## 选哪个平台？（首次使用必读）

同一个 Skill 可以连两个平台，用哪一个由**你的支付方式**决定，不是按国籍/IP：

| | **胜算云（中国大陆）** | **CogFoundry（国际）** |
|---|---|---|
| 支付方式 | 中国大陆支付（支付宝 / 微信 / 银联） | 国外信用卡（Visa / Mastercard） |
| 价格 | ¥0.5 / 次 | $0.10 / 次 |
| 服务地址 | `https://loomloom.shengsuanyun.com/loom/v1` | `https://loomloom.cogfoundry.ai/loom/v1` |
| 密钥申请 | console.shengsuanyun.com | CogFoundry 控制台 |
| token 变量 | `LOOMLOOM_TOKEN_SHENGSUANYUN` | `LOOMLOOM_TOKEN_COGFOUNDRY` |

> **怎么选**：你能用中国大陆支付 → 用胜算云；你能用国外信用卡 → 用 CogFoundry。
> 不确定能充哪个 → 两个都看，选你实际能充值的那一个。

## 安装 LoomLoom

### 方式 A：一句话安装（推荐）

把下面这段话粘贴给任意 AI 助手（**把平台地址换成你上面选的那一个**）：

> 请你在这个项目里安装 LoomLoom：安装地址是
> https://github.com/Cogfoundry-ai/loomloom 或
> https://gitee.com/cogfoundry/loomloom
> 服务地址：【你选平台的 server，见上表】
> Token 是【你选平台上申请的密钥】。
> 安装好之后帮我运行一次 doctor 检查是否正常。

### 方式 B：手动安装

1. 按上表去你选平台的**控制台申请 API 密钥**（胜算云：console.shengsuanyun.com；CogFoundry：CogFoundry 控制台）
2. 克隆仓库并按 README 安装：
   ```bash
   git clone https://gitee.com/cogfoundry/loomloom.git
   ```
3. 在 `~/.zshrc` 或 `~/.bashrc` 配置环境变量（**用你选那行的 server 和 token 变量名**）：
   - 胜算云（中国大陆支付）：
     ```bash
     export LOOMLOOM_SERVER='https://loomloom.shengsuanyun.com/loom/v1'
     export LOOMLOOM_TOKEN_SHENGSUANYUN='your-shengsuanyun-api-key'
     ```
   - CogFoundry（国外信用卡）：
     ```bash
     export LOOMLOOM_SERVER='https://loomloom.cogfoundry.ai/loom/v1'
     export LOOMLOOM_TOKEN_COGFOUNDRY='your-cogfoundry-api-key'
     ```
4. 验证（用你选平台的 server）：
   ```bash
   source ~/.zshrc
   loomloom doctor -s "$LOOMLOOM_SERVER"
   ```

## 没有 LoomLoom 也能用

未安装 LoomLoom 时，本 Skill 以**本地快速模式**运行：
Agent 自行联网检索课程目录、按你的目标推荐、排课并做冲突检测。
Excel 生成和校验脚本在两种模式下表现一致。

## 云端执行流程（市场买家路径）

1. **本地采集（必须先做）**：Agent 联网检索学校官网培养方案/课程手册，
   整理出课程目录文本。云端管道不联网，空目录只会得到占位输出。

2. **发现 SkillBot 并下载工作簿**：
   ```bash
   loomloom market list
   loomloom market show <listing-id>
   loomloom market workbook download <listing-id> --output-file input.xlsx
   ```

3. **填写工作簿**：每行一个学生——学校、教育体系、专业、年级、
   规划模式、目标与时间偏好、课程目录文本（第 1 步采集好的）、学期信息。

4. **校验 + 报价**：
   ```bash
   loomloom market workbook validate <listing-id> --file input.xlsx
   loomloom market workbook quote <listing-id> --file input.xlsx
   ```

5. **把平台预估费用给学生看，获得明确确认**（未确认不提交）。

6. **执行**（每次执行生成新的 client-request-id）：
   ```bash
   loomloom market workbook run <listing-id> --file input.xlsx \
     --confirm --client-request-id <unique-id>
   ```

7. **取回结果**：
   ```bash
   loomloom usage list
   loomloom usage get <run-transaction-id>
   ```

8. 把结果整理进本 Skill 的 JSON 输入格式（见 cloud-output-format.md），
   交给 `scripts/generate_excel.py` 与 `scripts/generate_ics.py` 生成文件。

> 注意：云端管道的内部提示词与步骤定义属于作者私有资产，
> 买家通过 Listing 调用即可，无需也无法查看内部实现。
