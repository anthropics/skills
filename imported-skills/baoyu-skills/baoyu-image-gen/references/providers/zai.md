# Z.AI GLM-Image

Read when the user picks `--provider zai` or sets `default_model.zai`. Default model is `glm-image`.

## Models

**`glm-image`** (recommended default)

- Text-to-image only in baoyu-image-gen (no `--ref` support yet)
- Native `quality` options are `hd` and `standard`; this skill maps `2k → hd` and `normal → standard`
- Recommended sizes: `1280x1280`, `1568x1056`, `1056x1568`, `1472x1088`, `1088x1472`, `1728x960`, `960x1728`
- Custom `--size` requires width/height in `[1024, 2048]`, divisible by `32`, total pixels ≤ `2^22`

**`cogview-4-250304`** (legacy family, same endpoint)

- Custom `--size` requires width/height in `[512, 2048]`, divisible by `16`, total pixels ≤ `2^21`

## Behavior Notes

- The sync API returns a temporary URL; baoyu-image-gen downloads it and writes locally
- `--ref` is not supported for Z.AI in this skill yet
- The sync API returns a single image, so `--n > 1` is rejected

## Official References

- [GLM-Image Guide](https://docs.z.ai/guides/image/glm-image)
- [Generate Image API](https://docs.z.ai/api-reference/image/generate-image)
