---
name: Smile Prediction Configuration
description: Uses visual AI generation models built-in alongside Python image composition to correct patient teeth smiles and create a before/after montage.
---

# Smile Prediction Montage Pipeline

This skill handles generating natural, well-maintained smiles using a set of pre-operation patient images (photos or 3D view scans) and creating a clean compilation montage with labels.

## Steps to Execute
1. Identify all images in the patient's `input-files` directory. Separate 2D face pictures from 3D intraoral scans.
2. For 2D face pictures: call your internal `generate_image` tool using the **Portrait Generation Prompt** below.
3. For multiple 3D scans: call your internal `generate_image` tool combining the 3D items into a single run using the **3D Unified Montage Prompt** below, which will directly output a tiled compilation with white backgrounds.
4. For 2D face pictures: Once the faces are generated and saved as artifacts, run the companion Python script `scripts/create_montage.py` for each original/generated pair to create and store the compilation in the patient's `output-files` directory.
5. Move generated 3D single montage images directly to the patient's `output-files` directory.

## Portrait Generation Prompt (2D Image)
```
Fix this person's teeth to create a natural, beautiful smile. Follow these rules strictly:
Only modify the teeth and immediate smile area. Do NOT alter the face shape, skin texture, skin tone, eyes, nose, hair, background, lighting, or any other aspect of the image. For example, don't change skin features, eyes (open or shut remain in initial state) etc.
Teeth should look naturally corrected — straightened, evenly sized, and properly aligned, as if the person had excellent orthodontic and dental work done.
Color should be natural and slightly whiter than average — think healthy, well-maintained teeth. Not Hollywood veneers. Not blue-white or glowing. A realistic, warm white.
Preserve the person's natural smile shape and lip position. Only adjust lips/surrounding area if the corrected teeth would naturally cause a subtle change (e.g., slightly fuller smile from straighter teeth).
Maintain photorealism at all times. The result should look like an untouched photograph, not an edited image. Match the lighting, resolution, grain, and color grading of the original exactly.
Do not change the input aspect ratio. The aspect ratio of the output must perfectly match the aspect ratio of the input.
Do not add or remove teeth beyond what is natural. If teeth are missing, you may fill them in. Do not give more teeth than a normal human smile would show.
Think very hard and reason carefully before making any changes.
```

## 3D Unified Montage Prompt (Tiled Output)
```
Orthodontic treatment, straighten teeth. Produce single image with all three input image modified and tiled into 3 straightened teeth images. Do same for "before" input images above modified ones. White background. Minimal explanatory text. Think very deepy and reason deeply before outputting. Think in 3D. Remove grey backgrounds and use pure white backgrounds for all pre and post 3d pictures. Do not change the input aspect ratio.
```

## Running the Script
Example script usage:
```bash
python3 .agents/skills/smile_prediction/scripts/create_montage.py --img_orig "/path/to/input.jpeg" --img_generated "/path/to/artifact.png" --output "/path/to/output_files/montage.jpg" --label "Upper Arch"
```
