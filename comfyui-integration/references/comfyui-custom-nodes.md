# ComfyUI Custom Nodes - Vetted Permissive License Nodes

## Overview

This document lists ComfyUI custom nodes evaluated for license compatibility. Only nodes with permissive licenses (MIT, Apache 2.0, BSD) are recommended for production use in proprietary applications using the API-only pattern.

## Core Recommended Nodes

### ComfyUI-GGUF (Apache 2.0)

**Repository:** https://github.com/city96/ComfyUI-GGUF

Enables quantized GGUF model inference (Llama, Mistral, etc.).

**Install:**
```bash
cd custom_nodes
git clone https://github.com/city96/ComfyUI-GGUF.git
```

**Key Nodes:**
- `GGUF_Loader` - Load GGUF models
- `GGUF_Sampler` - Generate text from GGUF models

**License:** Apache 2.0

### ComfyUI-KJNodes (MIT)

**Repository:** https://github.com/Kosinkadink/ComfyUI-KJNodes

Utility nodes for image/animation operations.

**Install:**
```bash
cd custom_nodes
git clone https://github.com/Kosinkadink/ComfyUI-KJNodes.git
```

**Key Nodes:**
- `Merge and Stack Images` - Combine multiple images
- `Image Batch to Sequence` - Convert batch operations
- `Animate Diff` - Animation generation

**License:** MIT

### ComfyUI-Manager (Apache 2.0)

**Repository:** https://github.com/ltdrdata/ComfyUI-Manager

Node and dependency manager for ComfyUI.

**Install:**
```bash
cd custom_nodes
git clone https://github.com/ltdrdata/ComfyUI-Manager.git
```

**Features:**
- Browse and install custom nodes
- Manage node dependencies
- Update nodes automatically

**License:** Apache 2.0

### Comfy-Downloader (MIT)

**Repository:** https://github.com/comfyanonymous/comfy-downloader

Model downloader and manager.

**Features:**
- Download models from Hugging Face
- Organize model directories
- Version management

**License:** MIT

### ImpactPack (MIT)

**Repository:** https://github.com/ltdrdata/ComfyUI-Impact-Pack

Advanced image analysis and processing nodes.

**Key Nodes:**
- `Detect and Segment` - Object detection
- `Mask Generation` - Create masks from detections
- `Iterative Sampling` - Advanced sampling patterns

**License:** MIT

### Flux Integration Nodes (MIT)

**Repository:** https://github.com/comfyanonymous/ComfyUI

Integrated Flux model support.

**Available in:** Core ComfyUI (check latest releases)

**Key Nodes:**
- `FluxLoader` - Load Flux models
- `FluxSampler` - Flux-specific sampling
- `T5TextEncode` - T5 text encoding for Flux

**License:** MIT (as part of ComfyUI)

## Image Processing Nodes

### Upscalers (MIT/Apache 2.0)

**Popular Options:**
- Real-ESRGAN upscaler nodes
- GFPGAN face enhancement
- Tile-based upscaling for large images

**Install:**
```bash
pip install realesrgan
```

**License:** MIT

### LoRA and Embedding Management (Apache 2.0)

**Features:**
- Load LoRA adapters
- Merge multiple LoRAs
- Quantize LoRA weights

## Workflow Templates

### Installing Recommended Node Set

```bash
cd ComfyUI/custom_nodes

# Package manager
git clone https://github.com/ltdrdata/ComfyUI-Manager.git

# GGUF support
git clone https://github.com/city96/ComfyUI-GGUF.git

# Utility nodes
git clone https://github.com/Kosinkadink/ComfyUI-KJNodes.git

# Advanced image processing
git clone https://github.com/ltdrdata/ComfyUI-Impact-Pack.git
```

### Checking Node Licenses

When adding new nodes:

1. **Check GitHub Repository**
   - Look for LICENSE file in root
   - Check license badge in README

2. **Verify Dependencies**
   ```bash
   pip show package_name
   # Check Home-page and License fields
   ```

3. **Audit Code**
   - Search for GPL imports or references
   - Check if node loads GPL libraries dynamically

4. **Legal Compliance**
   - Document license choice in your project
   - Maintain THIRD_PARTY_NOTICES.md
   - Update license scanning tools (FOSSA, Black Duck, etc.)

## Nodes to Avoid

### GPL/AGPL Licensed Nodes

These nodes should NOT be used in proprietary applications unless ComfyUI runs as a separate service:

- **AnimateDiff (original)** - Some versions under GPL
- **Custom nodes with unclear licensing** - Audit before use
- **Nodes importing GPL libraries** - E.g., GPL'd Python packages

### Problematic Patterns

Avoid nodes that:
- Dynamically load and execute arbitrary code
- Embed GPL'd binaries without clear isolation
- Have unaudited dependency chains
- Lack clear license documentation

## License Audit Template

```markdown
# Custom Node: [Node Name]

- **Repository:** [URL]
- **Author:** [Name]
- **Node License:** [MIT/Apache 2.0/etc.]
- **Key Dependencies:**
  - Dep1: [License]
  - Dep2: [License]
- **Audit Status:** [APPROVED/NEEDS_REVIEW/REJECTED]
- **Notes:** [Any relevant information]
- **Approved By:** [Name/Team]
- **Date:** [YYYY-MM-DD]
```

## Contributing Audited Nodes

If you audit a node successfully, document it:

1. Copy the audit template above
2. Complete all fields
3. Commit to `node-audits/` directory
4. Share results with team

## Integration Best Practices

### Node Organization

```
custom_nodes/
├── comfyui-manager/          # Package manager
├── comfyui-gguf/             # GGUF support
├── kjnodes/                  # Utility nodes
├── impact-pack/              # Image processing
└── LICENSES.md               # Centralized license docs
```

### Dependency Management

Keep `requirements.txt` for custom node dependencies:

```
# Custom Node Dependencies
real-esrgan>=0.3.0
gfpgan>=1.3.8
# Avoid GPL packages:
# numpy-scipy (has GPL deps)
```

### Version Pinning

Pin custom node versions for reproducibility:

```bash
# Record exact versions
pip freeze > custom_nodes_requirements.txt

# In CI/production
pip install -r custom_nodes_requirements.txt
```

## Monitoring Updates

Custom nodes update frequently. Establish a monitoring process:

1. **Weekly Checks**
   - Run `ComfyUI-Manager` update checker
   - Review release notes for breaking changes

2. **License Tracking**
   - Monitor for license changes in critical nodes
   - Update audit documents quarterly

3. **Security**
   - Pin versions in production
   - Test updates in staging before production

## Resources

- **ComfyUI Custom Nodes Index:** https://github.com/comfyanonymous/ComfyUI/wiki/Custom-Nodes
- **License Compatibility:** https://www.apache.org/licenses/GPL-compatibility.html
- **SPDX License List:** https://spdx.org/licenses/

## Legal Disclaimer

This document provides guidance only. Consult with legal counsel regarding license compliance for your specific use case. The API-only separation pattern reduces but does not eliminate GPL licensing concerns.
