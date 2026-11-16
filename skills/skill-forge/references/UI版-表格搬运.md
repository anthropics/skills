# UI 版（表格搬运）全链路

> 什么时候走到这里：录制里**根本没有**能直接取数的 XHR（服务端渲染 / 鉴权在页面里 / 接口加密），
> 只能把「A 页面下载的表」搬到「B 页面的在线表格」。这是兜底方案，不是主轴。

## 四步

1. **推断**
   ```bash
   python -I scripts/analyze.py --recording X.rec.json --source 源表.xlsx --out 草稿 --link 名
   ```
   产出：映射字典草稿、唯一键候选、定位库、路由表、`映射核对表.html`
2. **人工确认**：打开 `映射核对表.html` 勾选 → 导出 `映射核对_确认.csv` 放回草稿目录
   ```bash
   python -I scripts/analyze.py --confirm 草稿/映射核对_确认.csv --out 草稿
   ```
   产出：`链路就绪.json`
3. **生成**
   ```bash
   node scripts/build_skill.mjs --type ui --link 名 --config 草稿
   ```
4. **预览 → 真跑 → 记账**
   ```bash
   node scripts/run.mjs --config 配置 --source 新导出.xlsx        # 预览，不写
   node scripts/run.mjs --config 配置 --source 新导出.xlsx --go   # 真跑
   node scripts/manage.mjs pass --link 名
   ```

## 映射口径（不变）

- **按值对齐，不按列位置**；列名相同只算加分；拿不准就列出来让人选，别猜。
- 多张源表用逗号分隔；`--key 日期,视频id` 可直接指定唯一键跳过候选。

## 配置夹里五份文件各管什么

空白模板在 `templates/` 下（拍平命名）：`配置夹-映射字典.csv` / `配置夹-唯一键.csv` / `配置夹-路由表.csv` / `配置夹-同义字典.csv` / `配置夹-参数位.md`，复制到链路配置目录里改。

| 文件 | 作用 |
|---|---|
| `映射字典.csv` | 源表列 → 目标列的对应关系（按值对齐的结果） |
| `唯一键.csv` | 每行唯一标识，用于跑完回读核对「一行都不能少」 |
| `路由表.csv` | 源表的哪一类行，贴到目标页面哪个区域 |
| `同义字典.csv` | 列名不同但意思相同的写法（如「消耗/花费/成本」） |
| `参数位.md` | 人工填写的位置说明（目标页的第几个格子） |

## 什么算跑通（UI 版）

预览列头与值对得上；真跑后**每行唯一键都能在目标页回读见到**，差一行 = 失败。
失败就 `manage.mjs fail`，不许默默跳过。

## 产物

`produced/<链路>/`：`配置/`（上面几张表 + `接口.json` 或路由表）+ `scripts/`（`run.mjs` / `lib-cdp.mjs` / `lib-tableread.mjs`）+ `SKILL.md`（来自 `templates/child.SKILL.md`，含 `## 收尾`）。
