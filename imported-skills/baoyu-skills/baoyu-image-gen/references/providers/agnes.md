# Sapiens AI Agnes Image

Read when the user picks `--provider agnes` or sets `default_model.agnes`. Default model is `agnes-image-2.1-flash`.

## Models

**`agnes-image-2.1-flash`** (only model)

- Text-to-image and image-to-image (with `--ref`) in a single `/images/generations` endpoint
- Supports reference images as public URLs or Data URI (base64)
- Optimized for high information density, complex layouts, and rich details
- Size rules: both dimensions divisible by 32 (720px exception), long edge ≤ 2048, total pixels ≤ ~4M
- Default size: `1024x1024`; custom `--size` supports arbitrary WxH within the above rules
- `--ar` supported: computed as 2048-based size (long edge ≤ 2048, short edge proportional, both snapped to 32px); `1:1` special-cased to `1024x1024`

## Response Format

- The sync API always returns a URL
- Default (`--response-format file`): downloads the image and saves as `.png`
- Pass `--response-format url`: writes the URL string to `.txt` instead

## `--n` Behavior

The Agnes API returns a single image per request regardless of the `n` parameter. Passing `--n > 1` triggers a local error from `validateArgs` before any API call is made.

## Behavior Notes

- API key required: `AGNES_API_KEY`
- Base URL: `https://apihub.agnes-ai.com/v1` (override with `AGNES_BASE_URL`)
- Model override: `AGNES_IMAGE_MODEL` env
- `response_format` is always embedded in `extra_body` (not at request top level)
- Reference images: local files converted to Data URI base64 inline; remote URLs passed through
- Rate limit defaults: concurrency=3, startIntervalMs=1100 (override via `BAOYU_IMAGE_GEN_AGNES_CONCURRENCY` / `BAOYU_IMAGE_GEN_AGNES_START_INTERVAL_MS`)
- Timeout: 120s per request

## Size Resolution

- `--size <WxH>` wins over `--ar`
- `--ar` maps to a concrete size using the algorithm: long edge ≤ 2048, short edge proportional, both dimensions snapped to 32px
- `--ar 1:1` is special-cased to `1024x1024`

### Common `--ar` Results

| Aspect Ratio | Result |
|--------------|--------|
| `1:1` | `1024x1024` |
| `16:9` | `2048x1152` |
| `4:3` | `2048x1536` |
| `3:2` | `2048x1376` |
| `21:9` | `2048x896` |
| Unlisted ratio | Computed on the fly (portrait mirror swaps width/height) |

## Official References

- [Agnes AIGC API Hub](https://apihub.agnes-ai.com)
