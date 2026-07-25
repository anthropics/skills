# DashScope (阿里通义万象)

Read when the user picks `--provider dashscope`, sets `default_model.dashscope`, or asks for Qwen-Image behavior. The SKILL.md only names the default — this file covers model families, sizing rules, and limits.

## Model Families

**`qwen-image-2.0*`** — recommended modern family. Members: `qwen-image-2.0-pro`, `qwen-image-2.0-pro-2026-03-03`, `qwen-image-2.0`, `qwen-image-2.0-2026-03-03`.

- Free-form `size` in `宽*高` format
- Total pixels must be between `512*512` and `2048*2048`
- Default ≈ `1024*1024`
- Best choice for custom ratios (e.g. `21:9`) and text-heavy Chinese/English layouts

**Fixed-size family** — `qwen-image-max`, `qwen-image-max-2025-12-30`, `qwen-image-plus`, `qwen-image-plus-2026-01-09`, `qwen-image`.

- Only five sizes allowed: `1664*928`, `1472*1104`, `1328*1328`, `1104*1472`, `928*1664`
- Default is `1664*928`
- `qwen-image` currently has the same capability as `qwen-image-plus`

**`wan2.7-image*`** — multimodal Wan 2.7 family. Members: `wan2.7-image-pro`, `wan2.7-image`.

- Free-form `size` in `宽*高` format, plus aspect-ratio inference
- `wan2.7-image-pro` text-to-image (no `--ref`): total pixels in `[768*768, 4096*4096]`, ratio in `[1:8, 8:1]`
- `wan2.7-image-pro` with reference images and `wan2.7-image` (all scenarios): total pixels in `[768*768, 2048*2048]`, ratio in `[1:8, 8:1]`
- Default: `1024*1024` (`--quality normal`) or `2048*2048` (`--quality 2k`); 4K requires explicit `--size`
- Supports up to 9 reference images in `--ref` (image editing / multi-image fusion)
- Reference images are sent inline as base64 (or passed through if the path is an `http(s)://` URL)
- API does NOT use `prompt_extend`; the skill omits it for this family
- The Wan 2.7 API defaults `n` to **4** in non-collage mode and bills per generated image. baoyu-image-gen forces `n: 1` and rejects `--n > 1` to avoid silently paying for and discarding extra images.

**Legacy** — `z-image-turbo`, `z-image-ultra`, `wanx-v1`. Only use when the user explicitly asks for legacy behavior.

## Size Resolution

- `--size` wins over `--ar`
- For `qwen-image-2.0*`: prefer explicit `--size`; otherwise infer from `--ar` using the recommended table below
- For `qwen-image-max/plus/image`: only use the five fixed sizes; if the requested ratio doesn't fit, switch to `qwen-image-2.0-pro`
- For `wan2.7-image*`: explicit `--size` is validated against the per-mode pixel/ratio limits; otherwise the size is derived from `--ar` and `--quality` (`normal` ≈ 1K, `2k` ≈ 2K). To request 4K with `wan2.7-image-pro` text-to-image, pass `--size` explicitly (e.g. `4096*4096`, `3840*2160`)
- `--quality` is a baoyu-image-gen preset, not an official DashScope field. The mapping of `normal`/`2k` onto the `qwen-image-2.0*` and `wan2.7-image*` tables is an implementation choice, not an API guarantee

### Recommended `qwen-image-2.0*` sizes

| Ratio | `normal` | `2k` |
|-------|----------|------|
| `1:1` | `1024*1024` | `1536*1536` |
| `2:3` | `768*1152` | `1024*1536` |
| `3:2` | `1152*768` | `1536*1024` |
| `3:4` | `960*1280` | `1080*1440` |
| `4:3` | `1280*960` | `1440*1080` |
| `9:16` | `720*1280` | `1080*1920` |
| `16:9` | `1280*720` | `1920*1080` |
| `21:9` | `1344*576` | `2048*872` |

## Reference Images

- Only `wan2.7-image-pro` and `wan2.7-image` accept `--ref`. Other DashScope models (qwen-image-2.0*, qwen-image-max/plus/image, legacy) reject `--ref` and the user is steered to a different provider/model.
- Up to 9 reference images per request. Local files are inlined as base64 data URLs; `http(s)://` URLs are forwarded as-is.
- Supplying any `--ref` automatically clamps the wan2.7-image-pro pixel ceiling from 4K to 2K (the API only supports 4K for pure text-to-image with no image input).

## Not Exposed

DashScope APIs also support `negative_prompt`, `prompt_extend`, `watermark`, `thinking_mode`, `seed`, `bbox_list`, `enable_sequential`, and `color_palette`. `baoyu-image-gen` does not expose them as CLI flags today; the wan2.7 family relies on the API defaults (e.g. `thinking_mode=true`). The skill always sends `n=1` for wan2.7 — if you want grid/collage mode you currently need to call the API directly.

## Official References

- [Qwen-Image API](https://help.aliyun.com/zh/model-studio/qwen-image-api)
- [Text-to-image guide](https://help.aliyun.com/zh/model-studio/text-to-image)
- [Qwen-Image Edit API](https://help.aliyun.com/zh/model-studio/qwen-image-edit-api)
- [Wan 2.7 image generation & editing API](https://help.aliyun.com/zh/model-studio/wan-image-generation-and-editing-api-reference)
