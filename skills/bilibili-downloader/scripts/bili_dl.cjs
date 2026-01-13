#!/usr/bin/env node
/**
 * B站视频下载工具 - Node.js版本
 * 支持通过命令行参数传入视频URL和保存目录
 */

const https = require('https');
const http = require('http');
const fs = require('fs');
const path = require('path'); // Import path module for joining paths

// --- Argument Parsing ---
const args = process.argv.slice(2); // Get arguments after node and script path
if (args.length < 2) {
    console.error('Usage: node download_bilibili_video.cjs <video_url> <save_directory>');
    console.error('Example: node download_bilibili_video.cjs https://www.bilibili.com/video/BV1abcde ./downloads');
    process.exit(1);
}
const VIDEO_URL_ARG = args[0];
const SAVE_DIR = args[1];
// --- End Argument Parsing ---

// Ensure save directory exists
if (!fs.existsSync(SAVE_DIR)){
    fs.mkdirSync(SAVE_DIR, { recursive: true });
    console.log(`Created save directory: ${SAVE_DIR}`);
}

/**
 * 从URL中提取BV号
 */
function extractBVID(url) {
    // If it's already a BV number, return it
    if (url.startsWith('BV')) {
        return url;
    }
    // Extract BV number from the full URL
    const match = url.match(/BV[a-zA-Z0-9]+/);
    return match ? match[0] : null;
}

/**
 * 发送HTTP/HTTPS请求
 */
function fetch(url) {
    return new Promise((resolve, reject) => {
        const protocol = url.startsWith('https') ? https : http;
        const options = {
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                'Referer': 'https://www.bilibili.com/',
                'Origin': 'https://www.bilibili.com',
            }
        };

        protocol.get(url, options, (res) => {
            let data = '';

            res.on('data', (chunk) => {
                data += chunk;
            });

            res.on('end', () => {
                try {
                    const jsonData = JSON.parse(data);
                    resolve(jsonData);
                } catch (error) {
                    reject(new Error(`JSON解析失败: ${error.message}`));
                }
            });
        }).on('error', (error) => {
            reject(error);
        });
    });
}

/**
 * 获取视频信息
 */
async function getVideoInfo(bvid) {
    const url = `https://api.bilibili.com/x/web-interface/view?bvid=${bvid}`;
    const data = await fetch(url);

    if (data.code !== 0) {
        console.error(`获取视频信息失败:`, data);
        return null;
    }

    return data.data;
}

/**
 * 获取视频播放URL
 */
async function getVideoPlayurl(bvid, cid) {
    const url = `https://api.bilibili.com/x/player/playurl?bvid=${bvid}&cid=${cid}&qn=80&fnval=16&fnver=0&fourk=1`;
    const data = await fetch(url);

    if (data.code !== 0) {
        console.error(`获取播放URL失败:`, data);
        return null;
    }

    return data.data;
}

/**
 * 下载文件
 */
function downloadFile(url, filename) {
    return new Promise((resolve, reject) => {
        const protocol = url.startsWith('https') ? https : http;
        const options = {
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                'Referer': 'https://www.bilibili.com/',
            }
        };

        const fullPath = path.join(SAVE_DIR, filename); // Use SAVE_DIR here
        console.log(`开始下载: ${fullPath}`);

        protocol.get(url, options, (res) => {
            const totalSize = parseInt(res.headers['content-length'] || '0', 10);
            let downloaded = 0;

            const fileStream = fs.createWriteStream(fullPath); // Write to the full path

            res.on('data', (chunk) => {
                downloaded += chunk.length;
                fileStream.write(chunk);

                const progress = totalSize > 0 ? ((downloaded / totalSize) * 100).toFixed(1) : 0;
                process.stdout.write(`\r下载进度: ${progress}%`);
            });

            res.on('end', () => {
                fileStream.end();
                console.log(`\n✅ 下载完成: ${fullPath}`);
                resolve();
            });

            res.on('error', (error) => {
                fileStream.end();
                reject(error);
            });
        }).on('error', (error) => {
            reject(error);
        });
    });
}

/**
 * 主函数
 */
async function main() {
    // Use the URL from command-line arguments
    const bvid = extractBVID(VIDEO_URL_ARG);
    if (!bvid) {
        console.error('无法从URL中提取BV号，请检查URL格式');
        return;
    }

    console.log(`视频BV号: ${bvid}`);

    // CID is still auto-detected if not provided via arguments (though not implemented for args yet)
    // For now, we rely on auto-detection from video info
    let cid = ''; // VIDEO_CID is removed as it's not passed via args

    console.log(`正在获取视频 ${bvid} 的信息以获取CID...`);
    const videoInfo = await getVideoInfo(bvid);
    if (videoInfo) {
        cid = videoInfo.cid;
        console.log(`获取到CID: ${cid}`);
        console.log(`视频标题: ${videoInfo.title}`); // Display title here
    } else {
        console.log('无法获取视频信息');
        return;
    }

    console.log(`正在获取视频 ${bvid} 的播放链接...`);
    const playData = await getVideoPlayurl(bvid, cid);

    if (!playData) {
        console.log('获取播放链接失败');
        return;
    }

    const dashData = playData.dash || {};
    const videos = dashData.video || [];

    if (videos.length === 0) {
        console.log('没有找到视频流');
        return;
    }

    // 选择最高质量的视频
    const video = videos.reduce((max, v) => (v.bandwidth > max.bandwidth ? v : max), videos[0]);
    const videoUrl = video.baseUrl;

    console.log(`视频质量: ${video.width}x${video.height}`);
    console.log(`视频编码: ${video.codecs || 'N/A'}`);
    console.log(`带宽: ${video.bandwidth}`);

    // 获取音频
    const audios = dashData.audio || [];
    let audioUrl = null;

    if (audios.length > 0) {
        // 选择最高质量的音频
        const audio = audios.reduce((max, a) => (a.bandwidth > max.bandwidth ? a : max), audios[0]);
        audioUrl = audio.baseUrl;
        console.log(`音频质量: ${audio.id}`);
        console.log(`音频编码: ${audio.codecs || 'N/A'}`);
        console.log(`带宽: ${audio.bandwidth}`);
    }

    // Download video and audio using the provided save directory
    const videoFilename = `${bvid}_video.mp4`;
    const audioFilename = `${bvid}_audio.mp4`;

    try {
        await downloadFile(videoUrl, videoFilename);
        if (audioUrl) {
            await downloadFile(audioUrl, audioFilename);
        }
    } catch (error) {
        console.error('下载过程中发生错误:', error);
    }
}

main();
