// ModelScope API Examples
// This file demonstrates various usage patterns for the ModelScope API JavaScript client

const { ModelScopeAPI, chatWithModel, generateImageFromText } = require('./modelscope-api');

// Example 1: Basic Chat Completion
async function example1_basicChat() {
    console.log('\n=== Example 1: Basic Chat Completion ===');

    const client = new ModelScopeAPI();
    const model = 'Qwen/Qwen2.5-7B-Instruct';
    const messages = [
        { role: 'user', content: 'Hello! How are you?' }
    ];

    try {
        const response = await client.chatCompletion(model, messages);
        console.log('Response:', response.choices[0].message.content);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 2: Streaming Chat Completion
async function example2_streamingChat() {
    console.log('\n=== Example 2: Streaming Chat Completion ===');

    const client = new ModelScopeAPI();
    const model = 'Qwen/Qwen2.5-7B-Instruct';
    const messages = [
        { role: 'user', content: 'Tell me a short story about space exploration.' }
    ];

    try {
        const stream = await client.chatCompletionStream(model, messages);
        console.log('Streaming response:');

        // Note: Node.js stream handling would require additional code
        // This is a simplified example
        const reader = stream.body.getReader();
        const decoder = new TextDecoder();

        while (true) {
            const { done, value } = await reader.read();
            if (done) break;

            const chunk = decoder.decode(value);
            const lines = chunk.split('\n').filter(line => line.trim());

            for (const line of lines) {
                if (line.startsWith('data: ')) {
                    const data = line.slice(6);
                    if (data === '[DONE]') continue;

                    try {
                        const parsed = JSON.parse(data);
                        const content = parsed.choices[0]?.delta?.content;
                        if (content) {
                            process.stdout.write(content);
                        }
                    } catch (e) {
                        // Ignore parsing errors
                    }
                }
            }
        }
        console.log('\n--- Stream complete ---');
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 3: Basic Image Generation
async function example3_basicImage() {
    console.log('\n=== Example 3: Basic Image Generation ===');

    const client = new ModelScopeAPI();
    const model = 'Tongyi-MAI/Z-Image-Turbo';
    const prompt = 'A beautiful sunset over mountains, painted in watercolor style';

    try {
        const imageUrl = await client.generateImage(model, prompt);
        console.log('Generated image URL:', imageUrl);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 4: Image Generation with LoRA
async function example4_imageWithLora() {
    console.log('\n=== Example 4: Image Generation with LoRA ===');

    const client = new ModelScopeAPI();
    const model = 'Tongyi-MAI/Z-Image-Turbo';
    const prompt = 'A futuristic city with flying cars';
    const lora = {
        lora_path: 'modelscope/Example-LoRA-Model',
        lora_weight: 0.8
    };

    try {
        const imageUrl = await client.generateImage(model, prompt, '752x1280', { lora });
        console.log('Generated image URL with LoRA:', imageUrl);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 5: Multiple LoRAs
async function example5_multipleLoras() {
    console.log('\n=== Example 5: Multiple LoRAs ===');

    const client = new ModelScopeAPI();
    const model = 'Tongyi-MAI/Z-Image-Turbo';
    const prompt = 'A magical forest with glowing creatures';
    const loras = {
        lora_paths: [
            'modelscope/Fantasy-Style-LoRA',
            'modelscope/Glowing-Effects-LoRA'
        ],
        lora_weights: [0.6, 0.4]
    };

    // Validate LoRA weights first
    if (!client.validateLoraWeights(loras)) {
        console.log('LoRA weights validation failed');
        return;
    }

    try {
        const imageUrl = await client.generateImage(model, prompt, '752x1280', {
            lora_paths: loras.lora_paths,
            lora_weights: loras.lora_weights
        });
        console.log('Generated image URL with multiple LoRAs:', imageUrl);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 6: Batch Image Generation
async function example6_batchImages() {
    console.log('\n=== Example 6: Batch Image Generation ===');

    const client = new ModelScopeAPI();
    const model = 'Tongyi-MAI/Z-Image-Turbo';
    const prompts = [
        'A serene Japanese garden in spring',
        'A bustling cyberpunk street at night',
        'A peaceful countryside with windmills',
        'An underwater city with bioluminescent creatures'
    ];

    try {
        const imageUrls = await client.batchGenerateImages(model, prompts);
        console.log('Generated image URLs:');
        imageUrls.forEach((url, index) => {
            if (url) {
                console.log(`${index + 1}. ${url}`);
            } else {
                console.log(`${index + 1}. Failed to generate`);
            }
        });
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 7: Quick Chat Function
async function example7_quickChat() {
    console.log('\n=== Example 7: Quick Chat Function ===');

    const model = 'Qwen/Qwen2.5-7B-Instruct';
    const message = 'What is the capital of France?';

    try {
        const response = await chatWithModel(model, message);
        console.log('Quick chat response:', response);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 8: Quick Image Function
async function example8_quickImage() {
    console.log('\n=== Example 8: Quick Image Function ===');

    const model = 'Tongyi-MAI/Z-Image-Turbo';
    const prompt = 'A cozy cabin in the woods during winter';

    try {
        const imageUrl = await generateImageFromText(model, prompt);
        console.log('Quick image URL:', imageUrl);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 9: Advanced Chat Parameters
async function example9_advancedChat() {
    console.log('\n=== Example 9: Advanced Chat Parameters ===');

    const client = new ModelScopeAPI();
    const model = 'Qwen/Qwen2.5-7B-Instruct';
    const messages = [
        { role: 'system', content: 'You are a helpful coding assistant.' },
        { role: 'user', content: 'Write a JavaScript function to reverse a string.' }
    ];

    const options = {
        temperature: 0.7,
        max_tokens: 500,
        top_p: 0.9,
        frequency_penalty: 0.1,
        presence_penalty: 0.1
    };

    try {
        const response = await client.chatCompletion(model, messages, options);
        console.log('Response with advanced parameters:');
        console.log(response.choices[0].message.content);
    } catch (error) {
        console.error('Error:', error.message);
    }
}

// Example 10: Error Handling
async function example10_errorHandling() {
    console.log('\n=== Example 10: Error Handling ===');

    const client = new ModelScopeAPI();

    // Test 1: Invalid API key
    try {
        const badClient = new ModelScopeAPI('invalid-api-key');
        await badClient.chatCompletion('Qwen/Qwen2.5-7B-Instruct', [
            { role: 'user', content: 'Hello' }
        ]);
    } catch (error) {
        console.log('Test 1 - Invalid API key caught:', error.message.substring(0, 50) + '...');
    }

    // Test 2: Invalid model
    try {
        await client.chatCompletion('invalid/model', [
            { role: 'user', content: 'Hello' }
        ]);
    } catch (error) {
        console.log('Test 2 - Invalid model caught:', error.message.substring(0, 50) + '...');
    }

    // Test 3: Invalid LoRA weights
    const invalidLoras = {
        lora_path: 'modelscope/Example-LoRA',
        lora_weight: 3.0 // Invalid: > 2
    };
    const isValid = client.validateLoraWeights(invalidLoras);
    console.log('Test 3 - Invalid LoRA weights validation:', isValid ? 'Passed' : 'Failed (as expected)');
}

// Run all examples
async function runAllExamples() {
    console.log('🚀 Running ModelScope API JavaScript Examples...\n');

    // Run examples sequentially to avoid overwhelming the API
    await example1_basicChat();
    await new Promise(resolve => setTimeout(resolve, 1000));

    // Skip streaming example for simplicity
    // await example2_streamingChat();

    await example3_basicImage();
    await new Promise(resolve => setTimeout(resolve, 2000));

    await example4_imageWithLora();
    await new Promise(resolve => setTimeout(resolve, 2000));

    await example5_multipleLoras();
    await new Promise(resolve => setTimeout(resolve, 2000));

    await example6_batchImages();
    await new Promise(resolve => setTimeout(resolve, 2000));

    await example7_quickChat();
    await new Promise(resolve => setTimeout(resolve, 1000));

    await example8_quickImage();
    await new Promise(resolve => setTimeout(resolve, 2000));

    await example9_advancedChat();
    await new Promise(resolve => setTimeout(resolve, 1000));

    await example10_errorHandling();

    console.log('\n✅ All examples completed!');
}

// Export examples for individual use
module.exports = {
    example1_basicChat,
    example2_streamingChat,
    example3_basicImage,
    example4_imageWithLora,
    example5_multipleLoras,
    example6_batchImages,
    example7_quickChat,
    example8_quickImage,
    example9_advancedChat,
    example10_errorHandling,
    runAllExamples
};

// Run examples if this file is executed directly
if (require.main === module) {
    runAllExamples().catch(console.error);
}