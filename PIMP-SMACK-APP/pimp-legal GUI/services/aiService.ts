import { GoogleGenAI } from "@google/genai";
import { LogEntry } from '../types';

// Initialize the GoogleGenAI client with the API key from the environment variable.
// As per guidelines, we assume process.env.API_KEY is pre-configured and valid.
const ai = new GoogleGenAI({ apiKey: process.env.API_KEY });

let logs: LogEntry[] = [];

export const getLogs = () => [...logs];

export const clearLogs = () => {
    logs = [];
};

const logEvent = (type: 'request' | 'response' | 'error', content: string, model: string) => {
    logs.push({
        timestamp: new Date().toISOString(),
        model,
        type,
        content
    });
};

export const generateLegalContent = async (
  prompt: string,
  context: string,
  modelId: string
): Promise<string> => {
  
  // --- GOOGLE GEMINI HANDLER ---
  if (modelId.startsWith('gemini')) {
    logEvent('request', `Prompt: ${prompt} | Context Length: ${context.length}`, modelId);

    try {
      // "Top of the line" logic implies using higher thinking budgets or better system instructions if available.
      // If user selected gemini-3-pro-preview, we use it directly.
      
      const response = await ai.models.generateContent({
        model: modelId, 
        contents: `
          Role: You are an expert legal drafter and document formatter.
          
          Context: 
          ${context}
          
          Task: 
          Draft a section for the document based on the following instruction: "${prompt}".
          
          Constraints:
          - Use formal, court-appropriate language.
          - Do not include conversational filler (e.g., "Here is the text").
          - Output ONLY the body text for the section.
          - Ensure citations are formatted correctly if referenced.
        `,
        config: {
          temperature: 0.2, // Low temp for precision
          topK: 40,
          topP: 0.95,
        }
      });

      const text = response.text || "Error: Empty response from model.";
      logEvent('response', text.substring(0, 100) + "...", modelId);
      return text;

    } catch (error: any) {
      logEvent('error', error.message, modelId);
      console.error("Gemini Generation Error:", error);
      throw error;
    }
  }

  // --- ANTHROPIC CLAUDE HANDLER (Option to Add) ---
  if (modelId.startsWith('claude')) {
      logEvent('error', 'Claude API not integrated yet', modelId);
      throw new Error(`Claude integration requires an Anthropic API Key. This is a placeholder for the '${modelId}' option.`);
  }

  // --- OPENAI GPT HANDLER (Option to Add) ---
  if (modelId.startsWith('gpt')) {
      logEvent('error', 'GPT API not integrated yet', modelId);
      throw new Error(`GPT integration requires an OpenAI API Key. This is a placeholder for the '${modelId}' option.`);
  }

  throw new Error(`Model ${modelId} is not supported.`);
};
