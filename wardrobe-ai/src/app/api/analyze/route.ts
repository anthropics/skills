import Anthropic from '@anthropic-ai/sdk';
import { NextRequest, NextResponse } from 'next/server';

const client = new Anthropic();

const SYSTEM_PROMPT = `You are a professional fashion stylist and personal wardrobe consultant with a sharp eye for detail, color theory, and style.
You analyze outfit photos to help people understand and celebrate their personal style.
Be warm, encouraging, and specific. Focus on the person's actual clothes — not their body.
Always respond with valid JSON matching exactly the schema provided.`;

const ANALYSIS_PROMPT = `Analyze the outfit in this photo and return a JSON object with this exact structure:

{
  "title": "A creative, memorable outfit title (3-5 words, like 'Sunday Linen Edit' or 'Power Casual Monday')",
  "description": "2-3 sentences describing the overall look, vibe, and how pieces work together",
  "style": "One style label (e.g. Casual Chic, Minimalist, Streetwear, Boho, Classic, Smart Casual, Athleisure, Business Formal, Romantic, Edgy)",
  "mood": "One evocative mood word or phrase (e.g. 'Effortlessly Cool', 'Polished & Professional', 'Weekend Wanderer')",
  "occasions": ["array", "of", "applicable", "occasions"],
  "seasons": ["array", "of", "applicable", "seasons"],
  "colors": [
    {"name": "Color name", "hex": "#hexcode", "percentage": 40}
  ],
  "items": [
    {"category": "top|bottom|dress|outerwear|shoes|bag|accessory|other", "name": "Specific item name", "fabric": "Fabric if visible", "color": "Item color"}
  ],
  "tips": [
    "3 specific, actionable styling tips for this outfit or these pieces"
  ],
  "versatilityScore": 7,
  "confidence": "One-sentence statement about when this outfit shines"
}

Rules:
- occasions must be from: casual, work, formal, sport, evening, weekend, travel
- seasons must be from: spring, summer, fall, winter, all-season
- colors: list 2-5 dominant colors with approximate percentage (must sum to ~100)
- items: list every distinct clothing item/accessory visible
- tips: be specific and actionable (e.g. "Swap the white sneakers for tan loafers to take this to a dinner setting")
- versatilityScore: integer 1-10 (how many different contexts this works for)
- If the photo doesn't show a clear outfit, still analyze what's visible

Return ONLY valid JSON, no markdown, no explanation.`;

export async function POST(req: NextRequest) {
  try {
    const { imageBase64, mediaType } = await req.json();

    if (!imageBase64 || !mediaType) {
      return NextResponse.json({ error: 'Missing imageBase64 or mediaType' }, { status: 400 });
    }

    const stream = client.messages.stream({
      model: 'claude-opus-4-6',
      max_tokens: 4096,
      thinking: { type: 'enabled', budget_tokens: 1024 },
      system: SYSTEM_PROMPT,
      messages: [
        {
          role: 'user',
          content: [
            {
              type: 'image',
              source: {
                type: 'base64',
                media_type: mediaType as 'image/jpeg' | 'image/png' | 'image/webp' | 'image/gif',
                data: imageBase64,
              },
            },
            {
              type: 'text',
              text: ANALYSIS_PROMPT,
            },
          ],
        },
      ],
    });

    const message = await stream.finalMessage();

    // Extract the JSON text block (thinking blocks come first)
    const textBlock = message.content.find((b) => b.type === 'text');
    if (!textBlock || textBlock.type !== 'text') {
      return NextResponse.json({ error: 'No text in response' }, { status: 500 });
    }

    // Parse and validate the JSON
    let analysis;
    try {
      // Strip any accidental markdown fences
      const raw = textBlock.text.replace(/^```json\s*/i, '').replace(/```\s*$/, '').trim();
      analysis = JSON.parse(raw);
    } catch {
      return NextResponse.json(
        { error: 'Invalid JSON from model', raw: textBlock.text },
        { status: 500 }
      );
    }

    return NextResponse.json({ analysis });
  } catch (error) {
    const msg = error instanceof Error ? error.message : 'Unknown error';
    return NextResponse.json({ error: msg }, { status: 500 });
  }
}
