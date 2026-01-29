## 2024-05-23 - pdf2image Optimization
**Learning:** `pdf2image.convert_from_path` with `size` parameter is significantly faster (5x) than converting at full resolution and resizing with PIL, as it leverages `pdftoppm`'s native scaling and avoids large memory allocations.
**Action:** Always check if library wrappers expose native scaling/filtering options before implementing them in Python.

## 2024-05-24 - openpyxl read_only optimization
**Learning:** `openpyxl.load_workbook(..., read_only=True)` is significantly faster (1.75x) for parsing large files but requires explicit `wb.close()` (preferably in `try...finally`) as it keeps file handles open and `Workbook` objects may not support context managers in all versions.
**Action:** Use `read_only=True` for read-heavy Excel tasks and always ensure `close()` is called.
