"""
《递归的诅咒 / 模型崩溃》5 分钟科普视频 —— Manim 场景

依据论文: The Curse of Recursion (Shumailov et al., 2024, arXiv:2305.17493)

场景一览:
  1. HookScene        钩子: 人类内容 vs AI 内容 两条曲线交叉   (~30s)
  2. GaussianCollapse 核心: 一维高斯反复 采样->拟合->再采样   (~32s)
  3. TailCutoff       直方图砍掉 prob<1/M 的尾部, 解释 1/M     (~38s)
  4. GMMMerge         两峰 GMM 逐代纠缠合并                     (~28s)
  5. LLMTextScene     OPT-125m Gen 0/1/7/9 文本对比 (jackrabbit)(~35s)
  6. ConclusionScene  收尾: 原创数据越来越值钱                  (~20s)

渲染示例:
  .venv/bin/manim -qm scenes.py GaussianCollapse
  .venv/bin/manim -qm -a scenes.py        # 渲染全部场景

所有随机数据来自 model_collapse_data.py (固定种子), 场景内不跑随机数。
"""

import numpy as np
from manim import *

from model_collapse_data import (
    GAUSS_MEANS,
    GAUSS_STDS,
    GMM_HISTORY,
    hook_curves,
)

# ---- 全局风格 ----
config.background_color = "#0d1117"
CJK = "PingFang SC"          # macOS 自带中文字体
BLUE_C = "#4ea1ff"
ORANGE_C = "#ff9f43"
RED_C = "#ff5c5c"
GREEN_C = "#2ecc71"
GREY_C = "#5b6470"


def cn(text, **kwargs):
    """中文 Text 快捷方式。"""
    kwargs.setdefault("font", CJK)
    return Text(text, **kwargs)


def gauss_pdf(x, mu, sigma):
    return np.exp(-0.5 * ((x - mu) / sigma) ** 2) / (sigma * np.sqrt(2 * np.pi))


# ======================================================================
# 0. 开场:论文精读引入
# ======================================================================
class IntroScene(Scene):
    def construct(self):
        tag = cn("论文精读", font_size=28, color=ORANGE_C).to_edge(UP, buff=0.8)
        self.play(FadeIn(tag), run_time=0.8)

        cn_title = cn("《递归的诅咒》", font_size=58, color=WHITE, weight=BOLD)
        cn_sub = cn("在生成数据上训练，会让模型遗忘", font_size=30, color="#c9d1d9")
        en_title = Text(
            "The Curse of Recursion:\nTraining on Generated Data Makes Models Forget",
            font=CJK, font_size=26, color=BLUE_C, line_spacing=1.1,
        )
        meta = cn("Shumailov et al. · 牛津/剑桥/帝国理工 等 · arXiv:2305.17493 (2024)",
                  font_size=22, color=GREY_C)
        group = VGroup(cn_title, cn_sub, en_title, meta).arrange(DOWN, buff=0.5)
        group.move_to(ORIGIN).shift(UP * 0.2)

        self.play(Write(cn_title), run_time=1.5)
        self.wait(1.0)
        self.play(FadeIn(cn_sub, shift=UP * 0.1), run_time=1.0)
        self.wait(2.5)
        self.play(FadeIn(en_title), run_time=1.0)
        self.wait(2.0)
        self.play(FadeIn(meta), run_time=0.8)
        self.wait(2.5)

        invite = cn("今天，我们一起来精读这篇论文。", font_size=34, color=YELLOW)
        invite.to_edge(DOWN, buff=0.9)
        self.play(Write(invite), run_time=1.8)
        self.wait(4.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 1. 钩子场景
# ======================================================================
class HookScene(Scene):
    def construct(self):
        # 旁白: 训练 GPT 这样的大模型, 需要海量的人类文本。
        title = cn("GPT 的训练数据，快用完了。", font_size=42, color=WHITE)
        title.to_edge(UP, buff=0.5)
        self.play(FadeIn(title, shift=DOWN * 0.3), run_time=1.5)
        self.wait(2.5)

        axes = Axes(
            x_range=[0, 10, 2],
            y_range=[0, 7, 2],
            x_length=9,
            y_length=4.4,
            tips=False,
            axis_config={"include_numbers": False, "color": GREY_C},
        ).shift(DOWN * 0.5)
        x_label = cn("时间 →", font_size=24, color=GREY_C).next_to(axes.x_axis, RIGHT, buff=0.15)
        y_label = cn("内容产出量", font_size=22, color=GREY_C).next_to(axes.y_axis, UP, buff=0.15)
        self.play(Create(axes), FadeIn(x_label), FadeIn(y_label), run_time=1.2)
        self.wait(0.5)

        human_fn = lambda t: hook_curves(np.array([t]))[0][0]
        llm_fn = lambda t: min(hook_curves(np.array([t]))[1][0], 7.0)

        human_curve = axes.plot(human_fn, x_range=[0, 10], color=BLUE_C, stroke_width=6)
        llm_curve = axes.plot(llm_fn, x_range=[0, 10], color=ORANGE_C, stroke_width=6)

        # 标签放在各自曲线清晰、互不重叠的区域
        human_tag = cn("人类原创内容", font_size=26, color=BLUE_C)
        human_tag.next_to(axes.c2p(2.3, human_fn(2.3)), UP, buff=0.25)
        llm_tag = cn("AI 生成内容", font_size=26, color=ORANGE_C)
        llm_tag.next_to(axes.c2p(8.8, 7.0), UP, buff=0.15)

        # 旁白: 一个尴尬的事实——高质量人类文本快被用完了。
        self.play(Create(human_curve), FadeIn(human_tag), run_time=2.0)
        self.wait(2.0)
        # 旁白: 与此同时, AI 生成内容正在指数级暴涨。
        self.play(Create(llm_curve), FadeIn(llm_tag), run_time=2.5)
        self.wait(2.5)

        # 交叉点
        ts = np.linspace(0.1, 10, 5000)
        h, l = hook_curves(ts)
        cross_t = float(ts[np.argmin(np.abs(h - l))])
        cross_y = human_fn(cross_t)
        dot = Dot(axes.c2p(cross_t, cross_y), color=RED_C, radius=0.1)
        vline = DashedLine(
            axes.c2p(cross_t, 0), axes.c2p(cross_t, cross_y), color=RED_C, stroke_width=3
        )
        self.play(Create(vline), GrowFromCenter(dot), run_time=1.2)

        # 旁白: 用不了多久, 网上 AI 内容就会超过人类。
        q = cn("AI 生成内容即将超过人类内容", font_size=32, color=RED_C)
        q.to_edge(UP, buff=0.55)
        self.play(FadeOut(title), FadeIn(q, shift=DOWN * 0.2), run_time=1.2)
        self.wait(3.0)

        # 旁白: 能不能用 AI 生成的数据, 去训练下一代 AI?
        punch = cn("那……用 AI 生成的数据来训练 AI，行不行？", font_size=32, color=YELLOW)
        punch.to_edge(DOWN, buff=0.45)
        self.play(Write(punch), run_time=2.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 2. 核心场景: 一维高斯递归崩溃
# ======================================================================
class GaussianCollapse(Scene):
    def construct(self):
        means, stds = GAUSS_MEANS, GAUSS_STDS
        peak_max = float(np.max(1.0 / (stds * np.sqrt(2 * np.pi))))
        ymax = max(0.5, peak_max * 1.12)

        # 旁白: 我们先做个最简单的实验。
        title = cn("实验:让一个高斯分布反复「自我学习」", font_size=32, color=WHITE)
        title.to_edge(UP, buff=0.4)
        self.play(FadeIn(title), run_time=1.0)
        self.wait(2.0)

        axes = Axes(
            x_range=[-6, 6, 2],
            y_range=[0, ymax, 0.1],
            x_length=10,
            y_length=5,
            tips=False,
            axis_config={"color": GREY_C, "include_numbers": True, "font_size": 20},
        ).shift(DOWN * 0.3)
        self.play(Create(axes), run_time=1.2)

        # 旁白: 拿一个标准正态分布——它代表真实世界。
        curve0 = axes.plot(lambda x: gauss_pdf(x, means[0], stds[0]), color=BLUE_C, stroke_width=6)
        real_tag = cn("真实分布 N(0, 1)", font_size=24, color=BLUE_C)
        real_tag.next_to(axes.c2p(0, gauss_pdf(0, 0, 1)), UR, buff=0.1).shift(RIGHT * 0.6)
        self.play(Create(curve0), FadeIn(real_tag), run_time=1.5)
        self.wait(3.5)

        # 右上角实时数值
        gen_label = cn("第 0 代", font_size=28, color=WHITE)
        mu_label = Text("μ = %.2f" % means[0], font=CJK, font_size=26, color=ORANGE_C)  # ⚡ Text 不调 latex(原 MathTex 让本场景慢 2.4x)
        sigma_label = Text("σ = %.2f" % stds[0], font=CJK, font_size=26, color=GREEN_C)
        info = VGroup(gen_label, mu_label, sigma_label).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        info.to_corner(UR, buff=0.5).shift(DOWN * 0.4)
        self.play(FadeIn(info), run_time=0.8)

        # 旁白: 从当前分布采 100 个样本, 用均值/方差拟合下一代, 如此反复。
        recipe = cn("每代:采 100 个样本 → 用样本均值/方差拟合新高斯", font_size=22, color=GREY_C)
        recipe.to_edge(DOWN, buff=0.3)
        self.play(FadeIn(recipe), run_time=0.8)
        self.wait(4.5)

        # 关键叙述节拍: 在这些代数处停顿, 给旁白留时间
        pauses = {1: 1.5, 5: 2.5, 8: 2.0, 12: 2.5, 16: 2.0}
        traces = VGroup()
        prev_curve = curve0
        n_gen = len(means) - 1
        for n in range(1, n_gen + 1):
            mu, sig = means[n], stds[n]
            new_curve = axes.plot(
                lambda x, mu=mu, sig=sig: gauss_pdf(x, mu, sig),
                color=ORANGE_C,
                stroke_width=5,
            )
            # 旧曲线淡化成 trace
            faded = prev_curve.copy().set_stroke(opacity=0.18, color=GREY_C, width=2.5)
            traces.add(faded)

            new_gen = cn(f"第 {n} 代", font_size=28, color=WHITE).move_to(gen_label)
            new_mu = Text("μ = %.2f" % mu, font=CJK, font_size=26, color=ORANGE_C).move_to(mu_label)
            new_sig = Text("σ = %.2f" % sig, font=CJK, font_size=26, color=GREEN_C).move_to(sigma_label)

            rt = 1.5 if n <= 5 else (1.1 if n <= 12 else 0.9)
            self.add(faded)
            self.play(
                Transform(prev_curve, new_curve),
                Transform(gen_label, new_gen),
                Transform(mu_label, new_mu),
                Transform(sigma_label, new_sig),
                run_time=rt,
            )
            if n in pauses:
                self.wait(pauses[n])

        self.wait(1.0)
        # 旁白: 二十代后, 它离 N(0,1) 越来越远, 而且永远回不去了。
        verdict = cn("分布在漂移、变窄 —— 永远回不去 N(0,1) 了", font_size=28, color=RED_C)
        verdict.next_to(recipe, UP, buff=0.25)
        self.play(FadeOut(recipe), FadeIn(verdict), run_time=1.2)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 3. 尾部砍除场景
# ======================================================================
class TailCutoff(Scene):
    def construct(self):
        # 旁白: 为什么会这样? 根子在「采样」这两个字。
        title = cn("为什么会这样?稀有事件,根本采不到", font_size=32, color=WHITE)
        title.to_edge(UP, buff=0.4)
        self.play(FadeIn(title), run_time=0.8)
        self.wait(3.0)

        axes = Axes(
            x_range=[-4, 4, 1],
            y_range=[0, 0.45, 0.1],
            x_length=10,
            y_length=4.8,
            tips=False,
            axis_config={"color": GREY_C, "include_numbers": True, "font_size": 20},
        ).shift(DOWN * 0.3)
        self.play(Create(axes), run_time=0.8)

        # 直方图: 把 N(0,1) 离散成 bins
        n_bins = 24
        edges = np.linspace(-4, 4, n_bins + 1)
        centers = 0.5 * (edges[:-1] + edges[1:])
        width = edges[1] - edges[0]
        probs = gauss_pdf(centers, 0, 1)

        M = 100
        threshold = 1.0 / M  # 概率密度低于此, 100 个样本里基本采不到

        bars = VGroup()
        for c, p in zip(centers, probs):
            bottom = axes.c2p(c - width / 2, 0)
            top = axes.c2p(c + width / 2, p)
            bar = Rectangle(
                width=(top[0] - bottom[0]),
                height=(top[1] - bottom[1]),
                fill_color=BLUE_C,
                fill_opacity=0.85,
                stroke_color="#0d1117",
                stroke_width=1.5,
            )
            bar.move_to((bottom + top) / 2)
            bars.add(bar)
        # 旁白: 把分布画成直方图, 每根柱子是一种事件的概率; 中间常见, 两边稀有。
        self.play(LaggedStart(*[GrowFromEdge(b, DOWN) for b in bars], lag_ratio=0.04), run_time=2.0)
        self.wait(4.0)

        # 画出 1/M 阈值线
        thr_line = DashedLine(
            axes.c2p(-4, threshold), axes.c2p(4, threshold), color=YELLOW, stroke_width=3
        )
        thr_label = MathTex(r"p < \tfrac{1}{M} = \tfrac{1}{100}", font_size=32, color=YELLOW)
        thr_label.next_to(axes.c2p(4, threshold), UP, buff=0.1).shift(LEFT * 1.6)
        self.play(Create(thr_line), FadeIn(thr_label), run_time=1.2)

        # 所有叙述文字放在标题下方的顶部留白带, 避免与 x 轴刻度重叠
        text_anchor = title.get_bottom() + DOWN * 0.35
        explain = cn("只采 M=100 个样本 → 概率低于 1/M 的事件,期望出现次数 < 1",
                     font_size=22, color=GREY_C)
        explain.move_to([0, text_anchor[1], 0])
        # 旁白: 只采 100 个样本, 概率低于 1/M 的事件期望出现不到一次——基本采不到。
        self.play(FadeIn(explain), run_time=1.0)
        self.wait(5.0)

        # 砍掉尾部的 bin (低于阈值的)
        tail_bars = [b for b, p in zip(bars, probs) if p < threshold]
        keep_bars = [b for b, p in zip(bars, probs) if p >= threshold]
        for b in tail_bars:
            b.generate_target()
            b.target.set_fill(RED_C, opacity=0.9)
        # 旁白: 于是这些尾部, 被悄悄抹掉了。
        self.play(*[MoveToTarget(b) for b in tail_bars], run_time=0.8)
        self.play(
            LaggedStart(*[b.animate.shift(DOWN * 3).set_opacity(0) for b in tail_bars], lag_ratio=0.05),
            run_time=1.4,
        )
        self.wait(3.0)

        # 旁白: 信息一旦丢失, 就再也找不回来。
        lost = cn("尾部信息丢失,而且不可逆", font_size=28, color=RED_C)
        lost.move_to(explain)
        self.play(FadeOut(explain), FadeIn(lost), run_time=1.0)
        self.wait(3.0)

        # 下一代从被砍过的分布重新归一 -> 变窄
        kept_probs = np.array([p for p in probs if p >= threshold])
        kept_centers = np.array([c for c, p in zip(centers, probs) if p >= threshold])
        renorm = kept_probs / (kept_probs.sum() * width)
        # 重新计算每个保留 bar 的目标高度(归一后变高/变窄)
        for b, c, p in zip(keep_bars, kept_centers, renorm):
            base = axes.c2p(c, 0)
            top = axes.c2p(c, min(p, 0.44))
            new_h = top[1] - base[1]
            b.target = Rectangle(
                width=b.width,
                height=new_h,
                fill_color=ORANGE_C,
                fill_opacity=0.85,
                stroke_color="#0d1117",
                stroke_width=1.5,
            ).move_to([b.get_center()[0], base[1] + new_h / 2, 0])
        # 旁白: 下一代在被砍过的分布上重新归一, 于是更窄、尾巴更短。
        self.play(*[MoveToTarget(b) for b in keep_bars], run_time=1.4)
        self.wait(1.5)
        narrower = cn("下一代重新归一 → 分布更窄,尾巴更短", font_size=24, color=ORANGE_C)
        narrower.move_to(explain)
        self.play(FadeOut(lost), FadeIn(narrower), run_time=1.0)
        # 旁白: 一代一代, 分布不断向中间坍缩。
        self.wait(4.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 4. GMM 两峰合并
# ======================================================================
class GMMMerge(Scene):
    def gmm_pdf(self, x, w, mu, sig):
        return sum(
            w[k] * gauss_pdf(x, mu[k], sig[k]) for k in range(len(w))
        )

    def construct(self):
        title = cn("不只是高斯:两个峰会慢慢「纠缠」成一个", font_size=32, color=WHITE)
        title.to_edge(UP, buff=0.4)
        self.play(FadeIn(title), run_time=0.8)

        axes = Axes(
            x_range=[-5, 5, 1],
            y_range=[0, 0.75, 0.1],
            x_length=10,
            y_length=4.6,
            tips=False,
            axis_config={"color": GREY_C, "include_numbers": True, "font_size": 20},
        ).shift(DOWN * 0.3)
        self.play(Create(axes), run_time=0.8)

        # VAE 旁注放在标题下方, 避免在底部被裁掉
        note = cn("(VAE 生成的手写数字也一样:越来越像「平均数字」—— 见论文图 9)",
                  font_size=20, color=GREY_C)
        note.next_to(title, DOWN, buff=0.2)

        hist = GMM_HISTORY
        w0, mu0, sig0 = hist[0]
        # 旁白: 这不只是高斯分布的问题。换成两个峰的混合分布……
        curve = axes.plot(lambda x: self.gmm_pdf(x, w0, mu0, sig0), color=BLUE_C, stroke_width=6)
        tag = cn("真实分布:两个清晰的峰", font_size=24, color=BLUE_C).to_edge(DOWN, buff=0.45)
        self.play(Create(curve), FadeIn(tag), FadeIn(note), run_time=1.2)

        gen_label = cn("第 0 代", font_size=28, color=WHITE).to_corner(UR, buff=0.6).shift(DOWN * 0.6)
        self.play(FadeIn(gen_label))
        self.wait(3.0)

        # 旁白: 同样的过程让两个峰慢慢靠拢、互相纠缠。
        pauses = {6: 1.5, 9: 1.5}
        traces = VGroup()
        for n in range(1, len(hist)):
            w, mu, sig = hist[n]
            new_curve = axes.plot(
                lambda x, w=w, mu=mu, sig=sig: self.gmm_pdf(x, w, mu, sig),
                color=interpolate_color(ManimColor(BLUE_C), ManimColor(RED_C), n / (len(hist) - 1)),
                stroke_width=6,
            )
            faded = curve.copy().set_stroke(opacity=0.15, color=GREY_C, width=2)
            traces.add(faded)
            self.add(faded)
            new_gen = cn(f"第 {n} 代", font_size=28, color=WHITE).move_to(gen_label)
            self.play(
                Transform(curve, new_curve),
                Transform(gen_label, new_gen),
                run_time=1.05,
            )
            if n in pauses:
                self.wait(pauses[n])

        # 旁白: 最后塌成一个峰。VAE 生成的数字也越来越像「平均数字」。
        verdict = cn("模式纠缠 → 最终塌成一个尖峰", font_size=28, color=RED_C).move_to(tag)
        self.play(FadeOut(tag), FadeIn(verdict), run_time=1.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 5. 真实 LLM 文本对比 (OPT-125m)
# ======================================================================
class LLMTextScene(Scene):
    def construct(self):
        # 旁白: 那真正的大语言模型呢? 一样逃不掉。
        title = cn("真实的 LLM 也逃不掉:OPT-125m 微调 9 代", font_size=32, color=WHITE)
        title.to_edge(UP, buff=0.4)
        self.play(FadeIn(title), run_time=0.8)
        self.wait(2.5)

        # 旁白: 研究者拿 OPT-125m, 让它反复在自己生成的文本上微调九代。
        prompt = cn(
            "输入(关于英国教区教堂塔楼的维基段落)…",
            font_size=22,
            color=GREY_C,
        ).next_to(title, DOWN, buff=0.35)
        self.play(FadeIn(prompt), run_time=0.6)
        self.wait(3.5)

        def make_row(gen, text, color, highlight=None):
            tag = cn(gen, font_size=24, color=color, weight=BOLD)
            body = Text(
                text,
                font=CJK,
                font_size=20,
                color=WHITE,
                line_spacing=0.9,
                t2c=(highlight or {}),
            )
            body.set(width=min(body.width, 10.5))
            row = VGroup(tag, body).arrange(RIGHT, buff=0.3, aligned_edge=UP)
            return row

        g0 = make_row(
            "Gen 0",
            "…the earliest surviving example of Perpendicular Revival\narchitecture is found in the Church of Our Lady of Guernsey…",
            GREEN_C,
        )
        g1 = make_row(
            "Gen 1",
            "…such as St. Peter's Basilica in Rome or St. Peter's Basilica\nin Buenos Aires. There is no evidence that…",
            BLUE_C,
        )
        g7 = make_row(
            "Gen 7",
            "…In an interview with The New York Times, Wright said:\n\"I don't think there is anything wrong with me…\"",
            ORANGE_C,
        )
        g9 = make_row(
            "Gen 9",
            "…home to some of the world's largest populations of\nblack-tailed jackrabbits, white-tailed jackrabbits,\nblue-tailed jackrabbits, red-tailed jackrabbits, yellow-…",
            RED_C,
            highlight={
                "jackrabbits": RED_C,
                "black-tailed": RED_C,
                "white-tailed": RED_C,
                "blue-tailed": RED_C,
                "red-tailed": RED_C,
                "yellow-": RED_C,
            },
        )

        rows = VGroup(g0, g1, g7, g9).arrange(DOWN, aligned_edge=LEFT, buff=0.45)
        rows.next_to(prompt, DOWN, buff=0.45).to_edge(LEFT, buff=0.6)

        # 旁白逐代: Gen0 正常 / Gen1 张冠李戴 / Gen7 跑题闲聊 / Gen9 一本正经胡说
        row_holds = [4.5, 4.5, 5.0, 7.0]
        for r, hold in zip(rows, row_holds):
            self.play(FadeIn(r, shift=RIGHT * 0.2), run_time=1.1)
            self.wait(hold)

        # 旁白: 这就是模型崩溃在真实语言模型上的样子。
        punch = cn("到第 9 代,开始一本正经地胡说八道", font_size=28, color=RED_C)
        punch.to_edge(DOWN, buff=0.4)
        self.play(FadeIn(punch, shift=UP * 0.2), run_time=1.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 6. 收尾
# ======================================================================
class ConclusionScene(Scene):
    def construct(self):
        l1 = cn("模型崩溃,是所有生成模型的宿命。", font_size=38, color=WHITE)
        l2 = cn("数学上可证:这种漂移是必然的 —— 不是 bug,是宿命。", font_size=26, color=GREY_C)
        top = VGroup(l1, l2).arrange(DOWN, buff=0.35).shift(UP * 1.2)
        # 旁白: 模型崩溃, 是所有生成模型共同的宿命。
        self.play(FadeIn(l1, shift=UP * 0.2), run_time=1.2)
        self.wait(2.0)
        # 旁白: 数学上可证, 这种漂移是必然的——不是 bug, 是宿命。
        self.play(FadeIn(l2), run_time=1.0)
        self.wait(3.0)

        # 旁白: 所以, 没被 AI 污染过的人类原创数据, 会越来越值钱。
        punch1 = cn("所以,没被 AI 污染过的人类原创数据", font_size=34, color=YELLOW)
        punch2 = cn("会越来越值钱。", font_size=44, color=YELLOW, weight=BOLD)
        bottom = VGroup(punch1, punch2).arrange(DOWN, buff=0.3).shift(DOWN * 1.0)
        self.play(Write(punch1), run_time=1.4)
        self.play(FadeIn(punch2, scale=1.15), run_time=1.2)
        self.wait(3.5)

        # 旁白: 你现在发的每一条原创内容, 都在悄悄升值。
        last = cn("你现在发的每一条原创内容,都在升值。", font_size=28, color=WHITE)
        last.to_edge(DOWN, buff=0.6)
        self.play(FadeIn(last, shift=UP * 0.2), run_time=1.2)
        self.wait(5.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.2)


# ======================================================================
# 7. 参考文献
# ======================================================================
class ReferencesScene(Scene):
    def construct(self):
        title = cn("参考文献", font_size=40, color=WHITE).to_edge(UP, buff=1.0)
        self.play(FadeIn(title, shift=DOWN * 0.2), run_time=1.0)

        authors = Text(
            "Ilia Shumailov · Zakhar Shumaylov · Yiren Zhao\n"
            "Yarin Gal · Nicolas Papernot · Ross Anderson",
            font=CJK, font_size=24, color="#c9d1d9", line_spacing=1.1,
        )
        paper = Text(
            "The Curse of Recursion:\nTraining on Generated Data Makes Models Forget",
            font=CJK, font_size=30, color=BLUE_C, line_spacing=1.1, weight=BOLD,
        )
        arxiv = Text("arXiv:2305.17493  (2024)", font=CJK, font_size=26, color=ORANGE_C)
        block = VGroup(authors, paper, arxiv).arrange(DOWN, buff=0.5).move_to(ORIGIN)
        self.play(FadeIn(authors), run_time=0.8)
        self.play(Write(paper), run_time=1.6)
        self.play(FadeIn(arxiv, shift=UP * 0.1), run_time=0.8)

        note = cn("片中 OPT-125m 文本(Gen 0/1/7/9)与 VAE 图 9 均出自该论文",
                  font_size=20, color=GREY_C).to_edge(DOWN, buff=0.9)
        self.play(FadeIn(note), run_time=0.8)
        self.wait(3.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.2)
