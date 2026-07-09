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

Each transition video uses Kling (or similar AI video generation tool). Prompts describe smooth transitions from start frame to end frame.

**⚠️ Variable Duration**: Per cinematic pacing strategy, durations are NOT uniform 3 seconds. See suggested durations below.

### Video 1: High School → Bachelor's (2-2.5 seconds)
```
Smooth cinematic transition: starting from a young student in Chinese high school uniform standing in a bright school corridor with warm morning light, gently and naturally transforming into the same person wearing a black bachelor's graduation gown with pink trim on a tree-lined campus path with the library in soft-focus background, gentle camera drift right, warm nostalgic golden color grading throughout, 2.5 seconds duration, seamless morphing transition
```

### Video 2: Bachelor's → Master's (2-2.5 seconds)
```
Smooth cinematic transition: starting from a graduate in black bachelor's gown on a campus tree-lined path with library background, gently transforming into the same person wearing a blue master's graduation gown on a golden ginkgo-lined autumn path with graduate school entrance in background, gentle camera movement, warm autumn amber tones intensifying, 2.5 seconds duration, seamless and natural transition
```

### Video 3: Master's → Doctoral (3-3.5 seconds)
```
Smooth cinematic transition: starting from a graduate in blue master's gown on a ginkgo-lined autumn path with graduate school gate, slowly and gracefully transforming into the same person wearing a red doctoral gown in front of a traditional Chinese ancient building with peach blossoms and visible "学术报告厅" plaque, gentle camera pull-in with slight zoom, warm tones becoming richer and more saturated, 3.5 seconds duration, dignified and deliberate transition giving this key moment more screen time
```

### Video 4: Doctoral → Diploma (2.5-3 seconds)
```
Smooth cinematic transition: starting from a doctoral graduate in red gown standing proudly before an ancient building with peach blossoms, camera gently pulls back and shifts perspective to a close-up of a doctoral diploma certificate resting on a sunlit wooden desk with the graduate's portrait visible and university name obscured, warm golden light rays across the desk, tones becoming softer and more muted, 3 seconds duration, transition from celebration to quiet reflection
```

### Video 5: Diploma → Memorial Book (2.5-3 seconds)
```
Smooth cinematic transition: starting from a doctoral diploma on a sunlit desk with golden light rays, gently transforming into a closed book with cover reading "毕业纪念册" in elegant Chinese typography resting on a warm surface with sunset-like ambient lighting, soft camera movement, the warmest and softest color palette of the entire sequence, nostalgic and sentimental atmosphere, 3 seconds duration, transition from reflection to closure
```

### Video 6: Memorial Book Ending Hold (3-4 seconds)
```
Cinematic final frame: the closed "毕业纪念册" book cover in warm sunset-like ambient light, slow gentle camera hold with very subtle breathing movement, the warmest muted golden tones suggesting fond memory and closure, sentimental atmosphere, first frame only — no end frame transition, slow fade to slightly darker/warmer in the final second, 4 seconds duration, emotional ending that gives the viewer time to absorb
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
