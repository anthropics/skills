// ModelScope API JavaScript Client
// This file provides a JavaScript interface for ModelScope API services

const fetch = require('node-fetch');

class ModelScopeAPI {
    /**
     * Initialize ModelScope API client
     * @param {string} apiKey - API key for ModelScope (optional, will use MODELSCOPE_API_KEY env var)
     * @param {string} baseUrl - Base URL for ModelScope API
     */
    constructor(apiKey = null, baseUrl = 'https://api-inference.modelscope.cn') {
        this.apiKey = apiKey || process.env.MODELSCOPE_API_KEY;
        if (!this.apiKey) {
            throw new Error('MODELSCOPE_API_KEY environment variable is not set');
        }
        this.baseUrl = baseUrl;
    }

    /**
     * Chat completion using OpenAI-compatible API
     * @param {string} model - Model ID for chat completion
     * @param {Array} messages - Array of message objects
     * @param {Object} options - Additional options (temperature, max_tokens, etc.)
     * @returns {Promise} Response from the API
     */
    async chatCompletion(model, messages, options = {}) {
        const url = `${this.baseUrl}/v1/chat/completions`;
        const payload = {
            model: model,
            messages: messages,
            ...options
        };

        try {
            const response = await fetch(url, {
                method: 'POST',
                headers: {
                    'Authorization': `Bearer ${this.apiKey}`,
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify(payload)
            });

            if (!response.ok) {
                const errorData = await response.json();
                throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
            }

            return await response.json();
        } catch (error) {
            console.error('Chat completion failed:', error.message);
            throw error;
        }
    }

    /**
     * Streaming chat completion
     * @param {string} model - Model ID for chat completion
     * @param {Array} messages - Array of message objects
     * @param {Object} options - Additional options
     * @returns {Promise} Stream response
     */
    async chatCompletionStream(model, messages, options = {}) {
        const url = `${this.baseUrl}/v1/chat/completions`;
        const payload = {
            model: model,
            messages: messages,
            stream: true,
            ...options
        };

        try {
            const response = await fetch(url, {
                method: 'POST',
                headers: {
                    'Authorization': `Bearer ${this.apiKey}`,
                    'Content-Type': 'application/json'
                },
                body: JSON.stringify(payload)
            });

            if (!response.ok) {
                const errorData = await response.json();
                throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
            }

            return response;
        } catch (error) {
            console.error('Streaming chat completion failed:', error.message);
            throw error;
        }
    }

    /**
     * Generate image asynchronously
     * @param {string} model - Model ID for image generation
     * @param {string} prompt - Text prompt for image generation
     * @param {string} size - Image size (default: '752x1280')
     * @param {Object} options - Additional options (negative_prompt, lora, etc.)
     * @returns {Promise} Image URL
     */
    async generateImage(model, prompt, size = '752x1280', options = {}) {
        const submitUrl = `${this.baseUrl}/v1/images/generations`;
        const payload = {
            model: model,
            prompt: prompt,
            size: size,
            ...options
        };

        try {
            // Submit task
            console.log(`🚀 Submitting image generation task for: "${prompt.substring(0, 50)}..."`);
            const response = await fetch(submitUrl, {
                method: 'POST',
                headers: {
                    'Authorization': `Bearer ${this.apiKey}`,
                    'Content-Type': 'application/json',
                    'X-ModelScope-Async-Mode': 'true'
                },
                body: JSON.stringify(payload)
            });

            if (!response.ok) {
                const errorData = await response.json();
                throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
            }

            const data = await response.json();
            const taskId = data.task_id;

            // Poll for completion
            return await this._pollTask(taskId);
        } catch (error) {
            console.error('Image generation failed:', error.message);
            throw error;
        }
    }

    /**
     * Poll task status until completion
     * @param {string} taskId - Task ID to poll
     * @returns {Promise} Image URL when complete
     */
    async _pollTask(taskId) {
        const pollUrl = `${this.baseUrl}/v1/tasks/${taskId}`;
        const headers = {
            'Authorization': `Bearer ${this.apiKey}`,
            'X-ModelScope-Task-Type': 'image_generation'
        };

        console.log(`⏳ Task ID: ${taskId}`);

        while (true) {
            try {
                const response = await fetch(pollUrl, { headers });

                if (!response.ok) {
                    throw new Error(`HTTP ${response.status}: ${await response.text()}`);
                }

                const data = await response.json();
                const status = data.task_status;

                if (status === 'SUCCEED') {
                    // Defensive check: sometimes SUCCEED but output_images not ready
                    if (data.output_images && data.output_images.length > 0) {
                        console.log(''); // New line after dots
                        return data.output_images[0];
                    }
                } else if (status === 'FAILED' || status === 'CANCELED') {
                    throw new Error(`Task failed with status: ${status}`);
                }

                // Wait 2 seconds before retry
                await new Promise(resolve => setTimeout(resolve, 2000));
                process.stdout.write('.'); // Print dot to indicate waiting
            } catch (error) {
                console.error('\n❌ Polling failed:', error.message);
                throw error;
            }
        }
    }

    /**
     * Batch generate multiple images
     * @param {string} model - Model ID for image generation
     * @param {Array} prompts - Array of prompt strings
     * @param {string} size - Image size (default: '752x1280')
     * @param {Object} options - Additional options
     * @returns {Promise} Array of image URLs
     */
    async batchGenerateImages(model, prompts, size = '752x1280', options = {}) {
        console.log(`🚀 Batch generating ${prompts.length} images...`);

        const promises = prompts.map(prompt =>
            this.generateImage(model, prompt, size, options)
                .catch(error => {
                    console.error(`Failed to generate image for prompt "${prompt}":`, error.message);
                    return null; // Return null for failed generations
                })
        );

        const results = await Promise.all(promises);
        const successful = results.filter(url => url !== null);

        console.log(`✅ Successfully generated ${successful.length}/${prompts.length} images`);
        return results;
    }

    /**
     * Validate LoRA weights
     * @param {Object} loraConfig - LoRA configuration object
     * @returns {boolean} Whether weights are valid
     */
    validateLoraWeights(loraConfig) {
        if (!loraConfig) return true;

        // Single LoRA
        if (loraConfig.lora_path && loraConfig.lora_weight !== undefined) {
            const weight = parseFloat(loraConfig.lora_weight);
            if (isNaN(weight) || weight < 0 || weight > 2) {
                console.error(`Invalid LoRA weight: ${loraConfig.lora_weight}. Must be between 0 and 2`);
                return false;
            }
        }

        // Multiple LoRAs
        if (loraConfig.lora_paths && loraConfig.lora_weights) {
            if (!Array.isArray(loraConfig.lora_paths) || !Array.isArray(loraConfig.lora_weights)) {
                console.error('LoRA paths and weights must be arrays');
                return false;
            }

            if (loraConfig.lora_paths.length !== loraConfig.lora_weights.length) {
                console.error('Number of LoRA paths and weights must match');
                return false;
            }

            const totalWeight = loraConfig.lora_weights.reduce((sum, weight) => {
                const w = parseFloat(weight);
                if (isNaN(w) || w < 0 || w > 2) {
                    console.error(`Invalid LoRA weight: ${weight}. Must be between 0 and 2`);
                    return sum;
                }
                return sum + w;
            }, 0);

            if (totalWeight > 2) {
                console.error(`Total LoRA weight (${totalWeight}) exceeds maximum of 2`);
                return false;
            }
        }

        return true;
    }

    /**
     * Get model information
     * @param {string} modelId - Model ID
     * @returns {Promise} Model information
     */
    async getModelInfo(modelId) {
        const url = `${this.baseUrl}/v1/models/${modelId}`;

        try {
            const response = await fetch(url, {
                headers: {
                    'Authorization': `Bearer ${this.apiKey}`
                }
            });

            if (!response.ok) {
                const errorData = await response.json();
                throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
            }

            return await response.json();
        } catch (error) {
            console.error('Failed to get model info:', error.message);
            throw error;
        }
    }

    /**
     * List available models
     * @param {Object} filters - Filter options
     * @returns {Promise} List of models
     */
    async listModels(filters = {}) {
        const url = new URL(`${this.baseUrl}/v1/models`);

        // Add query parameters
        Object.keys(filters).forEach(key => {
            url.searchParams.append(key, filters[key]);
        });

        try {
            const response = await fetch(url, {
                headers: {
                    'Authorization': `Bearer ${this.apiKey}`
                }
            });

            if (!response.ok) {
                const errorData = await response.json();
                throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
            }

            return await response.json();
        } catch (error) {
            console.error('Failed to list models:', error.message);
            throw error;
        }
    }
}

// Convenience functions for quick usage

/**
 * Quick chat with a model
 * @param {string} model - Model ID
 * @param {string} message - User message
 * @param {string} apiKey - API key (optional)
 * @param {Object} options - Additional options
 * @returns {Promise} Response message
 */
async function chatWithModel(model, message, apiKey = null, options = {}) {
    const client = new ModelScopeAPI(apiKey);
    const messages = [{ role: 'user', content: message }];

    try {
        const response = await client.chatCompletion(model, messages, options);
        return response.choices[0].message.content;
    } catch (error) {
        console.error('Quick chat failed:', error.message);
        throw error;
    }
}

/**
 * Quick image generation
 * @param {string} model - Model ID
 * @param {string} prompt - Image prompt
 * @param {string} size - Image size
 * @param {string} apiKey - API key (optional)
 * @param {Object} options - Additional options
 * @returns {Promise} Image URL
 */
async function generateImageFromText(model, prompt, size = '752x1280', apiKey = null, options = {}) {
    const client = new ModelScopeAPI(apiKey);

    try {
        const imageUrl = await client.generateImage(model, prompt, size, options);
        return imageUrl;
    } catch (error) {
        console.error('Quick image generation failed:', error.message);
        throw error;
    }
}

module.exports = {
    ModelScopeAPI,
    chatWithModel,
    generateImageFromText
};