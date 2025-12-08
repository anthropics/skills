
// 1. 检查 API Key
const apiKey = process.env.MODELSCOPE_API_KEY;
if (!apiKey) {
    console.error("❌ Error: MODELSCOPE_API_KEY environment variable is not set.");
    process.exit(1);
}

// 2. 处理参数
const prompt = process.argv[2];
const size = process.argv[3];

if (!prompt) {
    console.error("❌ Error: Please provide a prompt.");
    process.exit(1);
}

const BASE_URL = "https://api-inference.modelscope.cn";
const MODEL_ID = "Tongyi-MAI/Z-Image-Turbo";

/**
 * 提交任务函数
 * @param {string} prompt 
 * @returns 
 */
async function submitTask(prompt) {
    try {
        console.log(`🚀 Submitting task for: "${prompt.substring(0, 5)}..."`);

        const response = await fetch(
            `${BASE_URL}/v1/images/generations`,
            {
                method: 'POST',
                headers: {
                    "Authorization": `Bearer ${apiKey}`,
                    "Content-Type": "application/json",
                    "X-ModelScope-Async-Mode": "true" // 必须开启异步模式
                },
                body: JSON.stringify({
                    model: MODEL_ID,
                    prompt: prompt,
                    size: size ? size : '752x1280'
                })
            }
        );

        if (!response.ok) {
            const errorData = await response.json();
            throw new Error(`HTTP ${response.status}: ${JSON.stringify(errorData)}`);
        }

        const data = await response.json();
        return data.task_id;
    } catch (error) {
        console.error("❌ Submission failed:", error.message);
        process.exit(1);
    }
}

/**
 * 轮询状态函数
 * @param {string} taskId 
 * @returns 
 */
async function pollTask(taskId) {
    console.log(`⏳ Task ID: ${taskId}.`);

    const pollUrl = `${BASE_URL}/v1/tasks/${taskId}`;
    const headers = {
        "Authorization": `Bearer ${apiKey}`,
        "X-ModelScope-Task-Type": "image_generation" // 查询必须带这个头
    };

    while (true) {
        try {
            const response = await fetch(pollUrl, { headers });

            if (!response.ok) {
                throw new Error(`HTTP ${response.status}: ${await response.text()}`);
            }

            const data = await response.json();
            const status = data.task_status;

            if (status === 'SUCCEED') {
                // ModelScope 有时返回 SUCCEED 但 output_images 还没准备好，做个防御性检查
                if (data.output_images && data.output_images.length > 0) {
                    return data.output_images[0];
                }
            } else if (status === 'FAILED' || status === 'CANCELED') {
                throw new Error(`Task failed with status: ${status}`);
            }

            // 等待 2 秒后重试 (根据你提供的测试，生成约5-6秒，间隔2秒比较合适)
            await new Promise(resolve => setTimeout(resolve, 2000));
            process.stdout.write("."); // 打印点号表示正在等待
        } catch (error) {
            console.error("\n❌ Polling failed:", error.message);
            process.exit(1);
        }
    }
}

(async () => {
    try {
        const taskId = await submitTask(prompt);
        const imageUrl = await pollTask(taskId);
        console.log(`🎉 Success! Image url: ${imageUrl}`);

    } catch (error) {
        console.error("\n❌ Error:", error.message);
        process.exit(1);
    }
})();