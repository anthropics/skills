**重要提示：您必须按顺序完成这些步骤。不要跳到编写代码。**

如果您需要填写 PDF 表单，首先检查 PDF 是否具有可填写的表单字段。从此文件的目录运行此脚本：
 `python scripts/check_fillable_fields <file.pdf>`，然后根据结果转到"可填写字段"或"不可填写字段"并按照这些说明操作。

# 可填写字段
如果 PDF 具有可填写的表单字段：
- 从此文件的目录运行此脚本：`python scripts/extract_form_field_info.py <input.pdf> <field_info.json>`。它将使用此格式创建一个包含字段列表的 JSON 文件：
```
[
  {
    "field_id": (字段的唯一 ID),
    "page": (页码，从 1 开始),
    "rect": ([左、下、右、上] PDF 坐标中的边界框，y=0 是页面的底部),
    "type": ("text"、"checkbox"、"radio_group" 或 "choice"),
  },
  // 复选框具有 "checked_value" 和 "unchecked_value" 属性：
  {
    "field_id": (字段的唯一 ID),
    "page": (页码，从 1 开始),
    "type": "checkbox",
    "checked_value": (将字段设置为此值以选中复选框),
    "unchecked_value": (将字段设置为此值以取消选中复选框),
  },
  // 单选组具有可能选择的 "radio_options" 列表。
  {
    "field_id": (字段的唯一 ID),
    "page": (页码，从 1 开始),
    "type": "radio_group",
    "radio_options": [
      {
        "value": (将字段设置为此值以选择此单选选项),
        "rect": (此选项的单选按钮的边界框)
      },
      // 其他单选选项
    ]
  },
  // 多选字段具有可能选择的 "choice_options" 列表：
  {
    "field_id": (字段的唯一 ID),
    "page": (页码，从 1 开始),
    "type": "choice",
    "choice_options": [
      {
        "value": (将字段设置为此值以选择此选项),
        "text": (选项的显示文本)
      },
      // 其他选择选项
    ],
  }
]
```
- 使用此脚本将 PDF 转换为 PNG（每页一个图像）（从此文件的目录运行）：
`python scripts/convert_pdf_to_images.py <file.pdf> <output_directory>`
然后分析图像以确定每个表单字段的用途（确保将边界框 PDF 坐标转换为图像坐标）。
- 使用此格式创建一个 `field_values.json` 文件，其中包含要为每个字段输入的值：
```
[
  {
    "field_id": "last_name", // 必须与 `extract_form_field_info.py` 中的 field_id 匹配
    "description": "用户的姓氏",
    "page": 1, // 必须与 field_info.json 中的 "page" 值匹配
    "value": "Simpson"
  },
  {
    "field_id": "Checkbox12",
    "description": "如果用户年满 18 岁或以上，则选中的复选框",
    "page": 1,
    "value": "/On" // 如果这是复选框，使用其 "checked_value" 值来选中它。如果是单选按钮组，使用 "radio_options" 中的一个 "value" 值。
  },
  // 更多字段
]
```
- 从此文件的目录运行 `fill_fillable_fields.py` 脚本以创建填写的 PDF：
`python scripts/fill_fillable_fields.py <input pdf> <field_values.json> <output pdf>`
此脚本将验证您提供的字段 ID 和值是否有效；如果打印错误消息，请更正相应的字段并重试。

# 不可填写的字段
如果 PDF 没有可填写的表单字段，您将添加文本注释。首先尝试从 PDF 结构中提取坐标（更准确），然后在需要时回退到视觉估计。

## 步骤 1：首先尝试结构提取

运行此脚本以提取带有精确 PDF 坐标的文本标签、线条和复选框：
`python scripts/extract_form_structure.py <input.pdf> form_structure.json`

这将创建一个包含以下内容的 JSON 文件：
- **labels**：每个带有精确坐标（x0、top、x1、bottom，以 PDF 点为单位）的文本元素
- **lines**：定义行边界的水平线
- **checkboxes**：小方形矩形，是复选框（带有中心坐标）
- **row_boundaries**：从水平线计算的行的顶部/底部位置

**检查结果**：如果 `form_structure.json` 具有有意义的标签（对应于表单字段的文本元素），请使用**方法 A：基于结构的坐标**。如果 PDF 是扫描/基于图像的，并且很少或没有标签，请使用**方法 B：视觉估计**。

---

## 方法 A：基于结构的坐标（首选）

当 `extract_form_structure.py` 在 PDF 中找到文本标签时使用此方法。

### A.1：分析结构

阅读 form_structure.json 并识别：

1. **标签组**：形成单个标签的相邻文本元素（例如，"Last" + "Name"）
2. **行结构**：具有相似 `top` 值的标签在同一行中
3. **字段列**：条目区域在标签结束后开始（x0 = label.x1 + gap）
4. **复选框**：直接使用结构中的复选框坐标

**坐标系**：PDF 坐标，其中 y=0 在页面的顶部，y 向下增加。

### A.2：检查缺失元素

结构提取可能不会检测到所有表单元素。常见情况：
- **圆形复选框**：只有方形矩形被检测为复选框
- **复杂图形**：装饰性元素或非标准表单控件
- **褪色或浅色元素**：可能不会被提取

如果您在 PDF 图像中看到不在 form_structure.json 中的表单字段，您需要对那些特定字段使用**视觉分析**（请参阅下面的"混合方法"）。

### A.3：使用 PDF 坐标创建 fields.json

对于每个字段，从提取的结构中计算条目坐标：

**文本字段：**
- entry x0 = label x1 + 5（标签后的小间隙）
- entry x1 = 下一个标签的 x0 或行边界
- entry top = 与 label top 相同
- entry bottom = 下方的行边界线或 label bottom + row_height

**复选框：**
- 直接使用 form_structure.json 中的复选框矩形坐标
- entry_bounding_box = [checkbox.x0, checkbox.top, checkbox.x1, checkbox.bottom]

使用 `pdf_width` 和 `pdf_height` 创建 fields.json（表示 PDF 坐标）：
```json
{
  "pages": [
    {"page_number": 1, "pdf_width": 612, "pdf_height": 792}
  ],
  "form_fields": [
    {
      "page_number": 1,
      "description": "姓氏条目字段",
      "field_label": "姓氏",
      "label_bounding_box": [43, 63, 87, 73],
      "entry_bounding_box": [92, 63, 260, 79],
      "entry_text": {"text": "Smith", "font_size": 10}
    },
    {
      "page_number": 1,
      "description": "美国公民是复选框",
      "field_label": "是",
      "label_bounding_box": [260, 200, 280, 210],
      "entry_bounding_box": [285, 197, 292, 205],
      "entry_text": {"text": "X"}
    }
  ]
}
```

**重要**：使用 `pdf_width`/`pdf_height` 和直接来自 form_structure.json 的坐标。

### A.4：验证边界框

在填写之前，检查边界框是否有错误：
`python scripts/check_bounding_boxes.py fields.json`

这将检查相交的边界框和对于字体大小来说太小的条目框。在填写之前修复任何报告的错误。

---

## 方法 B：视觉估计（回退）

当 PDF 是扫描/基于图像的且结构提取未找到可用的文本标签时使用此方法（例如，所有文本显示为 "(cid:X)" 模式）。

### B.1：将 PDF 转换为图像

`python scripts/convert_pdf_to_images.py <input.pdf> <images_dir/>`

### B.2：初始字段识别

检查每个页面图像以识别表单部分并获得字段位置的**粗略估计**：
- 表单字段标签及其近似位置
- 条目区域（文本输入的线条、框或空白空间）
- 复选框及其近似位置

对于每个字段，请注意近似像素坐标（它们尚不需要精确）。

### B.3：缩放细化（对准确性至关重要）

对于每个字段，在估计位置周围裁剪一个区域以精确细化坐标。

**使用 ImageMagick 创建缩放裁剪：**
```bash
magick <page_image> -crop <width>x<height>+<x>+<y> +repage <crop_output.png>
```

其中：
- `<x>, <y>` = 裁剪区域的左上角（使用您的粗略估计减去填充）
- `<width>, <height>` = 裁剪区域的大小（字段区域加上每侧约 50px 填充）

**示例：** 要细化估计在 (100, 150) 左右的"名称"字段：
```bash
magick images_dir/page_1.png -crop 300x80+50+120 +repage crops/name_field.png
```

（注意：如果 `magick` 命令不可用，请尝试使用相同参数的 `convert`。）

**检查裁剪的图像**以确定精确坐标：
1. 确定条目区域开始的精确像素（标签后）
2. 确定条目区域结束的位置（下一个字段或边缘之前）
3. 确定条目线/框的顶部和底部

**将裁剪坐标转换回完整图像坐标：**
- full_x = crop_x + crop_offset_x
- full_y = crop_y + crop_offset_y

示例：如果裁剪从 (50, 120) 开始，并且条目框在裁剪内从 (52, 18) 开始：
- entry_x0 = 52 + 50 = 102
- entry_top = 18 + 120 = 138

**对每个字段重复此操作**，在可能的情况下将附近的字段分组到单个裁剪中。

### B.4：使用细化坐标创建 fields.json

使用 `image_width` 和 `image_height` 创建 fields.json（表示图像坐标）：
```json
{
  "pages": [
    {"page_number": 1, "image_width": 1700, "image_height": 2200}
  ],
  "form_fields": [
    {
      "page_number": 1,
      "description": "姓氏条目字段",
      "field_label": "姓氏",
      "label_bounding_box": [120, 175, 242, 198],
      "entry_bounding_box": [255, 175, 720, 218],
      "entry_text": {"text": "Smith", "font_size": 10}
    }
  ]
}
```

**重要**：使用 `image_width`/`image_height` 和来自缩放分析的细化像素坐标。

### B.5：验证边界框

在填写之前，检查边界框是否有错误：
`python scripts/check_bounding_boxes.py fields.json`

这将检查相交的边界框和对于字体大小来说太小的条目框。在填写之前修复任何报告的错误。

---

## 混合方法：结构 + 视觉

当结构提取对大多数字段有效但遗漏了一些元素（例如，圆形复选框、非标准表单控件）时使用此方法。

1. **使用方法 A** 处理在 form_structure.json 中检测到的字段
2. **将 PDF 转换为图像**以进行缺失字段的视觉分析
3. **使用缩放细化**（来自方法 B）处理缺失字段
4. **组合坐标**：对于来自结构提取的字段，使用 `pdf_width`/`pdf_height`。对于视觉估计的字段，您必须将图像坐标转换为 PDF 坐标：
   - pdf_x = image_x * (pdf_width / image_width)
   - pdf_y = image_y * (pdf_height / image_height)
5. **在 fields.json 中使用单一坐标系** - 将所有内容转换为带有 `pdf_width`/`pdf_height` 的 PDF 坐标

---

## 步骤 2：填写前验证

**始终在填写之前验证边界框：**
`python scripts/check_bounding_boxes.py fields.json`

这将检查：
- 相交的边界框（将导致重叠文本）
- 对于指定字体大小来说太小的条目框

在继续之前修复 fields.json 中的任何报告错误。

## 步骤 3：填写表单

填写脚本自动检测坐标系并处理转换：
`python scripts/fill_pdf_form_with_annotations.py <input.pdf> fields.json <output.pdf>`

## 步骤 4：验证输出

将填写的 PDF 转换为图像并验证文本放置：
`python scripts/convert_pdf_to_images.py <output.pdf> <verify_images/>`

如果文本位置错误：
- **方法 A**：检查您是否使用带有 `pdf_width`/`pdf_height` 的 form_structure.json 中的 PDF 坐标
- **方法 B**：检查图像尺寸是否匹配以及坐标是否为准确的像素
- **混合**：确保视觉估计字段的坐标转换正确
