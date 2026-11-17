- 检查是否具备相关依赖，若缺失则请求安装：

```bash
pip install edge-tts moviepy markdown

#安装一整套完美对齐、针对 Mermaid 优化的新一代测试版全家桶
npm install @marp-team/marp-cli@latest \
  @marp-team/marp-core@next \
  shiki \
  beautiful-mermaid \
  katex \
  @mathjax/src \
  @mathjax/mathjax-bbm-font-extension \
  @mathjax/mathjax-bboldx-font-extension \
  @mathjax/mathjax-dsfont-font-extension \
  @mathjax/mathjax-mhchem-font-extension

```

(注：若系统提示缺少 ffmpeg，需引导或自动通过 `apt-get install -y ffmpeg` 进行安装)
