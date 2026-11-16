---
name: ecommerce-material-studio
description: "电商素材工坊（中英双语）。用户需要生成电商主图、详情图、场景图、产品图合成、品牌叠加时使用。自动识别品类→匹配风格→场景感知合成→统一文字→自动质检→多平台适配→标准化交付。E-commerce product image studio: category detection, style matching, scene-aware compositing, text overlay, quality check, multi-platform adaptation, batch delivery."
version: 1.0.0
author: 涛哥
license: MIT
metadata:
  hermes:
    tags: [ecommerce, image-generation, product-photo, 电商, 主图, 素材, 场景图]
---

# 电商素材工坊 / E-commerce Material Studio

生成电商产品素材（主图/详情图/场景图）的一站式工具链。输入产品图片 → 自动完成品类识别、风格匹配、场景合成、文字叠加、质检、多平台适配、批量交付。

**One-stop pipeline for e-commerce product images: category detection → style matching → scene compositing → text overlay → quality check → platform adaptation → batch delivery.**

## 何时使用 / When to use

- 用户需要生成**电商主图/详情图**（如"帮我做一套剃须刀主图"）
- 需要**产品图合成到场景**（白底图 → 场景图）
- 需要**品牌叠加**（Logo/保障条/卖点文字/徽章）
- 需要**多平台尺寸适配**（淘宝/快手/抖音/拼多多/京东等 7 平台）
- 需要**批量生成**多个产品素材

## 使用流程 / Workflow

```bash
# 0. 环境依赖（一次性）
pip install Pillow numpy scipy

# 1. 品类识别：输入产品图 → 识别品类/风格
python3 scripts/category_detector.py product.png

# 2. 风格匹配：品类+价位+平台+品牌 → 推荐模板
python3 scripts/style_matcher.py --category 个护电器 --sub-category 剃须刀 --price 169 --platform kuaishou

# 3. 场景感知合成（核心）：场景图+产品图 → 按参照物尺度自动合成
python3 scripts/scene_aware_compositor.py --scene scene.jpg --product product.png --scene-type lifestyle_bathroom

# 4. 统一文字叠加（z-index 分层，自动避让）
python3 scripts/text_engine.py --image result.png --text "Type-C快充" --layout bottom_band

# 5. 自动质检（5 项检查）
python3 scripts/quality_check.py --dir ./output

# 6. 多平台尺寸适配
python3 scripts/platform_adapter.py --dir ./output --platform kuaishou

# 7. 标准化交付打包（自动生成使用指南+清单+zip）
python3 scripts/delivery_packager.py --project-dir ./output --product-name "示例产品"

# 8. 批量处理（多产品，断点续传）
python3 scripts/batch_processor.py --input products.json --output-dir ./batch --prepare
```

## 模块清单 / Modules

| 模块 | 功能 | 依赖 |
|:---|:---|:---|
| `category_detector.py` | 品类识别（色调/材质→子品类） | Pillow |
| `style_matcher.py` | 风格匹配（品类+价位+平台+品牌→模板） | 无 |
| `brand_loader.py` | 品牌配置加载（多品牌/Logo选择） | 无 |
| `text_engine.py` | 统一文字引擎（z-index/避让/对比度） | Pillow |
| `quality_check.py` | 自动质检（分辨率/可读性/Logo/完整/重叠） | Pillow |
| `preference_memory.py` | 偏好记忆（跨项目复用风格） | 无 |
| `batch_processor.py` | 批量处理（断点续传/重试/报告） | 无 |
| `platform_adapter.py` | 7 平台尺寸适配（resize/crop/压缩） | Pillow |
| `delivery_packager.py` | 交付打包（使用指南+清单+zip） | Pillow |
| `layout_engine.py` | 布局引擎（物理尺寸→像素比例） | 无 |
| `scene_aware_compositor.py` | 场景感知合成（参照物尺度/透视/景深） | Pillow+numpy+scipy |

## 数据文件 / Data (references/)

- `category_templates.json` — 12 品类场景模板库（推荐场景/prompt/配色/文字风格）
- `product_profiles.json` — 产品档案库（示例：example_shaver）
- `brand_profiles/langke.json` — 示例品牌配置（朗科=示例品牌，非真实）
- `brand_config_template.json` — 新建品牌模板
- `user_preferences.json` — 偏好记忆库（模板）

## 注意事项 / Notes

- **字体**：`text_engine.py` 需要中文字体（macOS: `/System/Library/Fonts/PingFang.ttc`，Linux: NotoSansCJK，Windows: msyh.ttc）——按需修改 `FONT_PATHS_BOLD`/`FONT_PATHS_REGULAR` 常量
- **品牌配置**：用 `brand_config_template.json` 新建自己的品牌（含 Logo 路径/色系/保障条）
- **合成模式**：`scene_aware_compositor.py` 支持场景感知模式（自动算尺度）和兼容模式（固定 scale）
- 参考数据中的"朗科/LangKe"为**示例品牌**，可直接替换为自己的品牌配置

## 💛 免费使用 · 自愿支持 / Free with optional support

**本技能完全免费使用。** 觉得好用、帮到你了，可以**自愿扫码支持**（金额随意，一杯咖啡即可）：

![支付宝收款码](assets/alipay_qr.jpg)

> 支持过我的人，后续 Pro 版/批量服务有优惠。
> 想提需求、反馈问题，欢迎到 Gitee 仓库提 Issue：https://gitee.com/tao6677/useful-tools
