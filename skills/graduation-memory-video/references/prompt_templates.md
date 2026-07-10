# Graduation Memory Video — Image & Video Prompt Templates

Complete prompt templates for generating 6 graduation scene images and 6 transition videos. Replace `[PERSON_DESCRIPTION]` with the extracted person features from the user's reference photo.

**⚠️ Person Consistency Critical Reminder**: Use EXACTLY the same `[PERSON_DESCRIPTION]` text across all 6 prompts — copy-paste without abbreviation or rephrasing. Consistency takes priority over brevity. If image-to-image mode is available, use it instead.

**Visual Style Unity**: All 6 images must present a unified visual style — warm cinematic color grading (golden hour / warm cinematic), documentary feel with slight artistic elevation, 9:16 vertical composition. Color tones progress from bright warm → amber deep → slightly saturated → soft muted, echoing emotional progression.

---

## Image 1: High School Graduation

```
A realistic cinematic portrait photo of [PERSON_DESCRIPTION], wearing a Chinese high school uniform (蓝白配色运动校服), standing in a bright school corridor with large windows letting in warm natural morning light, smiling warmly with youthful energy and optimism, soft golden hour color tones with warm highlights, cinematic film grain texture, shallow depth of field with blurred background, documentary photography style with slight cinematic elevation, 9:16 vertical aspect ratio, gentle and nostalgic atmosphere, the light creates a warm halo effect around the subject
```

Key: Chinese high school uniform (蓝白运动校服), bright warm corridor (golden hour), youthful smile. Shallow depth of field, film grain.

---

## Image 2: Bachelor's Graduation

```
A realistic cinematic portrait photo of [PERSON_DESCRIPTION], wearing a Chinese bachelor's degree graduation gown (黑色学士服 with 粉色领饰/粉垂 indicating arts/humanities), standing confidently on a tree-lined campus path with dappled warm sunlight filtering through green leaves, background shows the university library building in soft focus, warm spring golden hour lighting creating gentle shadows, cinematic film grain texture, shallow depth of field, documentary photography style with cinematic elevation, 9:16 vertical aspect ratio, scholarly and proud atmosphere, warm color palette with rich golden tones
```

Key: Bachelor's gown (black + pink trim), library background (soft focus), tree-lined path with dappled light, golden tones.

---

## Image 3: Master's Graduation

```
A realistic cinematic portrait photo of [PERSON_DESCRIPTION], wearing a Chinese master's degree graduation gown (蓝色硕士服 with 藏蓝色/深蓝领饰), standing on a beautiful ginkgo tree-lined path with golden autumn leaves creating a warm amber canopy, background shows the graduate school entrance gate with signage in soft focus, warm autumn golden tones with amber and burnt sienna highlights, cinematic film grain texture, shallow depth of field, the golden ginkgo leaves frame the subject naturally, documentary photography style with cinematic elevation, 9:16 vertical aspect ratio, mature and accomplished atmosphere, warm rich color palette
```

Key: Master's gown (blue + dark blue trim), ginkgo autumn path (amber tones), graduate school entrance (soft focus), warmer deeper tones than previous.

---

## Image 4: Doctoral Graduation

```
A realistic cinematic portrait photo of [PERSON_DESCRIPTION], wearing a Chinese doctoral degree graduation gown (红色博士服 with 红色领饰 and black trim), standing proudly in front of a traditional Chinese-style ancient building with a visible plaque that reads "学术报告厅" (Academic Lecture Hall) in clear Chinese characters, surrounded by blooming peach blossom trees (桃花) creating a soft pink-red frame, warm spring sunlight with gentle golden highlights, cinematic film grain texture, shallow depth of field with the ancient building softly blurred behind, documentary photography style with cinematic elevation, 9:16 vertical aspect ratio, dignified and scholarly atmosphere with a sense of culmination, warm and slightly more saturated color palette than previous scenes
```

Key: Doctoral gown (red + red trim), ancient building with "学术报告厅" plaque (MUST be visible), peach blossoms, slightly more saturated tones for "peak" feeling.

---

## Image 5: Doctoral Diploma

```
A realistic cinematic close-up photo of a Chinese doctoral diploma/graduation certificate placed on a polished wooden desk, warm golden sunlight slanting across the desk surface creating dramatic light rays and warm shadows, the certificate features [PERSON_DESCRIPTION]'s portrait photo in the upper corner, the certificate has ornate borders with traditional Chinese academic design elements in red and gold, the university name area is intentionally blurred or obscured (不显示校名), warm nostalgic lighting with slightly softer and more muted tones than previous scenes, cinematic film grain texture, shallow depth of field focused on the certificate, documentary photography style with cinematic elevation, 9:16 vertical aspect ratio, the overall mood transitions from bright celebration to quiet reflection
```

Key: Diploma on sunlit desk (golden light rays), portrait visible, university name MUST be obscured/blurred. Tones becoming softer — emotional shift from "celebration" to "reflection".

---

## Image 6: Memorial Book Cover

```
A realistic cinematic photo of a closed book resting on a warm surface, the book cover (书皮) clearly displays the title "毕业纪念册" (Graduation Memorial Book) in elegant Chinese typography with a warm nostalgic design, the cover features soft pastel colors with subtle decorative elements like small graduation cap motifs and delicate flower illustrations, warm ambient lighting with soft shadows and the gentle glow of sunset-like illumination, cinematic film grain texture, the book is positioned at a slight angle creating visual interest, shallow depth of field with surface texture visible, documentary photography style with cinematic elevation, 9:16 vertical aspect ratio, gentle and sentimental atmosphere, the overall color palette is the warmest and softest of all six scenes — muted golden tones suggesting closure and fond memory
```

Key: Closed book with "毕业纪念册" clearly visible, sunset-like warm lighting. Warmest and softest tones of all 6 — emotional "closure".

---

## Person Description Extraction Guide

From the user's reference photo, extract these features for `[PERSON_DESCRIPTION]`:

- Gender and approximate age
- Facial features (hair style/color, skin tone, distinctive features — be EXTREMELY detailed)
- Body features (height/build, posture habits)
- Overall vibe and style (intellectual, lively, gentle, etc.)
- Any features the user specifically emphasizes
- Clothing preferences (colors/styles favored)

**Critical**: The `[PERSON_DESCRIPTION]` must be identical text in all 6 prompts. Copy-paste, never rephrase.

Example: `a young Chinese woman in her late 20s, with long black hair flowing past her shoulders, warm brown eyes, gentle smile showing slightly dimpled cheeks, fair skin with warm undertones, slender build with graceful posture, warm and intellectual demeanor, wearing minimal natural makeup`

---

## Chinese Degree Gown Color Reference

| Degree Level | Gown Color | Trim Color | Visual Meaning |
|-------------|-----------|-----------|---------------|
| Bachelor's | Black | Pink trim (文科/arts) | Foundation, warm start |
| Master's | Blue | Dark blue/navy trim | Depth and rigor |
| Doctoral | Red | Red trim + black border | Peak achievement, honor |

Default uses pink trim (humanities). If user specifies a different discipline, adjust trim color accordingly.

---

## Transition Video Prompt Templates

Each transition video uses Kling's **First-Last Frame mode** — you provide a start frame image and an end frame image, and Kling AI-generates the smooth transition animation between them.

### ⚠️ How to Use

1. Upload the start frame image and end frame image to Kling
2. Enter the corresponding prompt text in Kling's text description field
3. Kling generates the smooth transition between the two images based on both the images and the prompt
4. **Video 6 is special**: Only upload Image 6 as start frame, no end frame — Kling generates a static hold + slow fade-out

**Critical Prompt Requirement**: Every prompt must emphasize **the transition should be smooth, natural, and aesthetically beautiful — no stiff or mechanical morphing, no abrupt cuts**. Transitions must be natural and graceful evolutions, not forced deformations or jump cuts.

**⚠️ Variable Duration**: Per cinematic pacing strategy, durations are NOT uniform 3 seconds. See suggested durations below.

### Video 1: High School → Bachelor's (Start frame=Image 1, End frame=Image 2, 2-2.5 seconds)
```
Kling first-last frame transition video. Start frame: a young student in Chinese high school uniform standing in a bright school corridor with warm morning light. End frame: the same person wearing a black bachelor's graduation gown with pink trim on a tree-lined campus path with library in soft-focus background. The transition should be smooth, natural, and aesthetically beautiful — the scene gently evolves from the school corridor to the campus path with the person's attire naturally morphing from school uniform to graduation gown, warm nostalgic golden color grading maintained throughout, gentle camera drift right, NO stiff or mechanical morphing, NO abrupt cuts, 2.5 seconds duration
```

### Video 2: Bachelor's → Master's (Start frame=Image 2, End frame=Image 3, 2-2.5 seconds)
```
Kling first-last frame transition video. Start frame: a graduate in black bachelor's gown on a campus tree-lined path with library background. End frame: the same person wearing a blue master's graduation gown on a golden ginkgo-lined autumn path with graduate school entrance in background. The transition should be smooth, natural, and aesthetically beautiful — the scene gently evolves from spring campus path to autumn ginkgo path with the gown color naturally shifting from black to blue, warm autumn amber tones gradually intensifying, gentle camera movement, NO stiff or mechanical morphing, NO abrupt cuts, 2.5 seconds duration
```

### Video 3: Master's → Doctoral (Start frame=Image 3, End frame=Image 4, 3-3.5 seconds)
```
Kling first-last frame transition video. Start frame: a graduate in blue master's gown on a ginkgo-lined autumn path with graduate school gate. End frame: the same person wearing a red doctoral gown in front of a traditional Chinese ancient building with peach blossoms and visible "学术报告厅" plaque. The transition should be smooth, natural, and aesthetically beautiful — the scene slowly and gracefully evolves from autumn ginkgo path to spring ancient building with peach blossoms, the gown naturally shifts from blue to red, warm tones becoming richer and more saturated, gentle camera pull-in with slight zoom, NO stiff or mechanical morphing, NO abrupt cuts, this key moment deserves more screen time with a dignified and deliberate pace, 3.5 seconds duration
```

### Video 4: Doctoral → Diploma (Start frame=Image 4, End frame=Image 5, 2.5-3 seconds)
```
Kling first-last frame transition video. Start frame: a doctoral graduate in red gown standing proudly before an ancient building with peach blossoms. End frame: a close-up of a doctoral diploma certificate resting on a sunlit wooden desk with the graduate's portrait visible and university name obscured. The transition should be smooth, natural, and aesthetically beautiful — the camera gently pulls back and shifts perspective from the person in graduation scene to the diploma on the desk, warm golden light rays gradually appear across the desk surface, tones becoming softer and more muted, NO stiff or mechanical morphing, NO abrupt cuts, this transition shifts emotional tone from celebration to quiet reflection, 3 seconds duration
```

### Video 5: Diploma → Memorial Book (Start frame=Image 5, End frame=Image 6, 2.5-3 seconds)
```
Kling first-last frame transition video. Start frame: a doctoral diploma on a sunlit desk with golden light rays. End frame: a closed book with cover reading "毕业纪念册" in elegant Chinese typography resting on a warm surface with sunset-like ambient lighting. The transition should be smooth, natural, and aesthetically beautiful — the scene gently evolves from the desk with diploma to the warm surface with the memorial book, the warmest and softest color palette of the entire sequence gradually emerging, soft camera movement, nostalgic and sentimental atmosphere intensifying, NO stiff or mechanical morphing, NO abrupt cuts, transition from reflection to closure, 3 seconds duration
```

### Video 6: Memorial Book Ending Hold (Start frame=Image 6, NO end frame, 3-4 seconds)
```
Kling first-frame-only video. Start frame: the closed "毕业纪念册" book cover in warm sunset-like ambient light. NO end frame provided — this is a final hold sequence. Slow gentle camera hold with very subtle breathing movement, the warmest muted golden tones suggesting fond memory and closure, sentimental atmosphere, slow fade to slightly darker/warmer in the final second, emotional ending that gives the viewer time to absorb, 4 seconds duration. The transition style should be natural and gentle — no abrupt changes, just a peaceful, lingering final moment
```

---

## Color Tone Progression Table

The 6 images follow a deliberate emotional color progression (not independently designed):

| Scene | Color Character | Emotional Mapping | Keywords |
|-------|----------------|-------------------|----------|
| High School | Bright warm, white-gold | Youthful beginnings | bright warm, golden highlights |
| Bachelor's | Rich golden, warm spring | Growing confidence | rich golden, warm spring |
| Master's | Amber warm, deeper | Depth and maturity | amber, burnt sienna |
| Doctoral | Slightly saturated, red-gold | Peak achievement | richer saturation, red-gold |
| Diploma | Soft muted yellow | Quiet reflection | muted golden, softer |
| Memorial Book | Warmest, softest sunset | Closure and fond memory | warmest, softest, sunset-like |
