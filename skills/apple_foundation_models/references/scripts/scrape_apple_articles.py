#\!/usr/bin/env python3
"""
Automatic Apple Documentation Article Scraper
"""
import asyncio
from playwright.async_api import async_playwright
import json

ARTICLES = [
    {"name": "generating_content", "url": "https://developer.apple.com/documentation/foundationmodels/generating-content-and-performing-tasks-with-foundation-models"},
    {"name": "prompting", "url": "https://developer.apple.com/documentation/foundationmodels/prompting-an-on-device-foundation-model"},
    {"name": "guided_generation", "url": "https://developer.apple.com/documentation/foundationmodels/generating-swift-data-structures-with-guided-generation"},
    {"name": "tool_calling", "url": "https://developer.apple.com/documentation/foundationmodels/expanding-generation-with-tool-calling"},
    {"name": "custom_adapters", "url": "https://developer.apple.com/documentation/foundationmodels/loading-and-using-a-custom-adapter-with-foundation-models"}
]

async def scrape_article(page, article):
    print(f"\n📄 {article['name']}...")
    try:
        await page.goto(article['url'], wait_until='networkidle', timeout=30000)
        await page.wait_for_selector('article, main', timeout=10000)
        
        title = await page.text_content('h1')
        content = await page.text_content('article, main')
        code_blocks = []
        for elem in await page.query_selector_all('pre code, pre'):
            code = await elem.inner_text()
            if code: code_blocks.append(code.strip())
        
        print(f"   ✓ {len(content)} chars, {len(code_blocks)} code blocks")
        return {'name': article['name'], 'title': title.strip(), 'content': content.strip(), 'code_blocks': code_blocks, 'success': True}
    except Exception as e:
        print(f"   ✗ {e}")
        return {'name': article['name'], 'error': str(e), 'success': False}

async def main():
    print("🚀 Scraping Apple Documentation...")
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        page = await browser.new_page()
        results = []
        for article in ARTICLES:
            results.append(await scrape_article(page, article))
            await asyncio.sleep(2)
        await browser.close()
    
    with open('output/apple_articles_scraped.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✅ Done\! {sum(1 for r in results if r['success'])}/{len(results)} successful")

if __name__ == "__main__":
    asyncio.run(main())
