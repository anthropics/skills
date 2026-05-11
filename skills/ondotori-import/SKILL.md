---
name: ondotori-import
description: "Use this skill when the user wants to convert CSV files exported from T&D Corporation's Ondotori (おんどとり) temperature/humidity data loggers into a formatted Excel spreadsheet. Trigger when the user provides one or more Ondotori CSV files and wants to organize the data into Excel. The skill creates one Excel sheet per sensor/CSV file, each containing date/time, temperature (°C), and humidity (%) columns. Do NOT trigger for general CSV-to-Excel conversions unrelated to Ondotori data loggers."
---

# Ondotori CSV → Excel Converter

Convert CSV files exported from T&D Corporation's Ondotori (おんどとり) temperature/humidity data loggers into a structured Excel workbook, with one sheet per sensor.

**What is Ondotori?** Ondotori is a series of wireless temperature and humidity data loggers made by T&D Corporation (Japan). They record environmental data at regular intervals and export it as CSV files.

---

## Prerequisites

Python 3.8 or later is required. Install the dependencies before running the script:

```bash
pip install pandas openpyxl
```

---

## Quickstart

Run the following commands from the `skills/ondotori-import/` directory:

```bash
# Single file
python scripts/ondotori_to_excel.py /path/to/sensor_A.csv

# Multiple files → one Excel workbook
python scripts/ondotori_to_excel.py /path/to/sensor_A.csv /path/to/sensor_B.csv --output result.xlsx
```

The output file `ondotori_data.xlsx` (or the name you specified with `--output`) is saved in the current directory.

No Ondotori device? Use the sample CSV in `scripts/sample_ondotori.csv` to verify the skill works:

```bash
python scripts/ondotori_to_excel.py scripts/sample_ondotori.csv
```

---

## When This Skill Triggers

- User provides `.csv` files exported from an Ondotori device
- User asks to convert, organize, or transcribe Ondotori sensor data into Excel
- User mentions "おんどとり", "温湿度データ", or "T&D" along with CSV files

---

## Workflow

### Step 1: Receive Files
Ask the user to provide their Ondotori CSV file(s) if not already shared. Multiple CSV files can be processed together into one Excel workbook.

### Step 2: Inspect CSV Format
Ondotori CSV files typically contain:
- A header block with device info at the top (automatically skipped)
- Data rows with: 日時 (datetime), 温度 (temperature in °C), 湿度 (humidity in %)

Common column name variations handled automatically:

| Column | Variants recognized |
|--------|---------------------|
| Datetime | 日時, 測定日時, Date/Time, DateTime |
| Temperature | 温度, 温度(℃), 温度(°C), CH1, Temperature |
| Humidity | 湿度, 湿度(%RH), 湿度(%), CH2, Humidity |

### Step 3: Run the Conversion Script

```bash
python scripts/ondotori_to_excel.py <csv_file1> [csv_file2 ...] --output <output.xlsx>
```

**Examples** (run from the `skills/ondotori-import/` directory):

```bash
# Convert a single file (output: ondotori_data.xlsx in current directory)
python scripts/ondotori_to_excel.py /path/to/room_A.csv

# Convert multiple files into one workbook
python scripts/ondotori_to_excel.py /path/to/room_A.csv /path/to/room_B.csv --output building.xlsx
```

### Step 4: Verify Output
The generated Excel file will contain:
- One sheet per CSV file, named after the sensor filename
- Columns: 日時, 温度(℃), 湿度(%)
- Header row is bold, highlighted, and frozen (stays visible when scrolling)
- Column widths are fitted to the widest value in each column
- Rows are sorted by datetime in ascending order
- Cell values starting with `=`, `+`, `-`, `@` are sanitized to prevent Excel formula injection

### Step 5: Deliver
Provide the output `.xlsx` file to the user and confirm:
- Number of sheets created
- Total data rows per sheet
- Date range covered

---

## Output Format

```
output.xlsx
├── Sheet "room_A"         ← named from CSV filename
│   ├── Row 1: 日時 | 温度(℃) | 湿度(%)   ← bold, highlighted header
│   ├── Row 2: 2024/01/01 00:00 | 23.5 | 45.2
│   ├── Row 3: 2024/01/01 00:10 | 23.6 | 45.1
│   └── ...sorted by datetime ascending
└── Sheet "room_B"
    └── ...
```

---

## Troubleshooting

| Problem | Cause | Solution |
|---------|-------|----------|
| `ModuleNotFoundError: pandas` | Dependencies not installed | Run `pip install pandas openpyxl` |
| `Could not find data header row` | Unrecognized column names | Check CSV column names and add them to the `*_VARIANTS` lists in the script |
| `Could not read {filename}` | Unusual file encoding | Ondotori exports are typically Shift-JIS or UTF-8; the script tries both automatically |
| Sheet name is truncated | Excel sheet names are limited to 31 characters | Expected behavior; the script truncates automatically |
| Missing humidity column | Sensor records temperature only | The sheet is created with datetime + temperature only; a warning is printed |
