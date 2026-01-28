## 2024-05-23 - pdf2image Optimization
**Learning:** `pdf2image.convert_from_path` with `size` parameter is significantly faster (5x) than converting at full resolution and resizing with PIL, as it leverages `pdftoppm`'s native scaling and avoids large memory allocations.
**Action:** Always check if library wrappers expose native scaling/filtering options before implementing them in Python.
