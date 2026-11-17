import { GoogleGenAI } from "@google/genai";
import { DocumentSection } from '../types';
import { v4 as uuidv4 } from 'uuid';

// Initialize the GoogleGenAI client with the API key from the environment variable.
// As per guidelines, we assume process.env.API_KEY is pre-configured and valid.
const ai = new GoogleGenAI({ apiKey: process.env.API_KEY });

export const generateSectionContent = async (
  prompt: string,
  context: string, // e.g., metadata, previous sections
  modelId: string = 'gemini-3-flash-preview'
): Promise<string> => {
  // Model selection logic
  // gemini-3-pro-preview is for complex tasks, gemini-3-flash-preview for speed/basic tasks.
  const modelName = modelId.includes('pro') ? 'gemini-3-pro-preview' : 'gemini-3-flash-preview';

  try {
    const response = await ai.models.generateContent({
      model: modelName,
      contents: `
        Context: ${context}
        
        Task: Draft a legal document section based on this prompt: "${prompt}".
        
        Style Guide: Formal, legal prose. No conversational filler. Return ONLY the text for the section body.
      `,
      config: {
        temperature: 0.3, // Lower temperature for more deterministic/formal output
      }
    });

    return response.text || "Error: No text generated.";
  } catch (error) {
    console.error("Gemini Generation Error:", error);
    throw error;
  }
};

export const refineText = async (
  text: string,
  instruction: string,
  modelId: string = 'gemini-3-flash-preview'
): Promise<string> => {
    const modelName = modelId.includes('pro') ? 'gemini-3-pro-preview' : 'gemini-3-flash-preview';

    const response = await ai.models.generateContent({
        model: modelName,
        contents: `
            Original Text: "${text}"
            
            Instruction: ${instruction}
            
            Return the revised text only.
        `
    });
    return response.text || text;
}
