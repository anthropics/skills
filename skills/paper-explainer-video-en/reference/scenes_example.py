"""
"The Curse of Recursion / Model Collapse" 5-minute explainer video — Manim scenes (ENGLISH)

Based on: The Curse of Recursion (Shumailov et al., 2024, arXiv:2305.17493)

Scene overview:
  1. HookScene        hook: human-content vs AI-content, two curves cross        (~30s)
  2. GaussianCollapse core: a 1-D Gaussian repeatedly sample -> fit -> resample  (~32s)
  3. TailCutoff       histogram cuts the prob<1/M tail, explains 1/M             (~38s)
  4. GMMMerge         a two-peak GMM entangles and merges over generations       (~28s)
  5. LLMTextScene     OPT-125m Gen 0/1/7/9 text comparison (jackrabbit)          (~35s)
  6. ConclusionScene  close: original human data only grows more valuable        (~20s)

Render examples:
  ~/llm_mc_venv/bin/manim -qm scenes.py GaussianCollapse
  ~/llm_mc_venv/bin/manim -qm -a scenes.py        # render all scenes

All random data comes from model_collapse_data.py (fixed seed); no random numbers inside scenes.
"""

import numpy as np
from manim import *

from model_collapse_data import (
    GAUSS_MEANS,
    GAUSS_STDS,
    GMM_HISTORY,
    hook_curves,
)

# ---- global style ----
config.background_color = "#0d1117"
LATIN = "Helvetica Neue"     # clean Latin font, always on macOS
BLUE_C = "#4ea1ff"
ORANGE_C = "#ff9f43"
RED_C = "#ff5c5c"
GREEN_C = "#2ecc71"
GREY_C = "#5b6470"


def txt(text, **kwargs):
    """English / Latin Text shortcut."""
    kwargs.setdefault("font", LATIN)
    return Text(text, **kwargs)


def gauss_pdf(x, mu, sigma):
    return np.exp(-0.5 * ((x - mu) / sigma) ** 2) / (sigma * np.sqrt(2 * np.pi))


# ======================================================================
# 0. Intro: paper deep-dive opener
# ======================================================================
class IntroScene(Scene):
    def construct(self):
        tag = txt("Paper Deep-Dive", font_size=28, color=ORANGE_C).to_edge(UP, buff=0.8)
        self.play(FadeIn(tag), run_time=0.8)

        title = txt("The Curse of Recursion", font_size=56, color=WHITE, weight=BOLD)
        sub = txt("Training on Generated Data Makes Models Forget",
                  font_size=28, color=BLUE_C)
        meta = txt("Shumailov et al. · Oxford / Cambridge / Imperial · arXiv:2305.17493 (2024)",
                   font_size=22, color=GREY_C)
        group = VGroup(title, sub, meta).arrange(DOWN, buff=0.55)
        group.move_to(ORIGIN).shift(UP * 0.2)

        self.play(Write(title), run_time=1.5)
        self.wait(1.0)
        self.play(FadeIn(sub, shift=UP * 0.1), run_time=1.0)
        self.wait(2.5)
        self.play(FadeIn(meta), run_time=0.8)
        self.wait(2.5)

        invite = txt("Today, let's read this paper together.", font_size=34, color=YELLOW)
        invite.to_edge(DOWN, buff=0.9)
        self.play(Write(invite), run_time=1.8)
        self.wait(4.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 1. Hook scene
# ======================================================================
class HookScene(Scene):
    def construct(self):
        # narration: training a large model like GPT takes a massive amount of human text.
        title = txt("GPT is running out of training data.", font_size=42, color=WHITE)
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
        x_label = txt("Time →", font_size=24, color=GREY_C).next_to(axes.x_axis, RIGHT, buff=0.15)
        y_label = txt("Volume of content", font_size=22, color=GREY_C).next_to(axes.y_axis, UP, buff=0.15)
        self.play(Create(axes), FadeIn(x_label), FadeIn(y_label), run_time=1.2)
        self.wait(0.5)

        human_fn = lambda t: hook_curves(np.array([t]))[0][0]
        llm_fn = lambda t: min(hook_curves(np.array([t]))[1][0], 7.0)

        human_curve = axes.plot(human_fn, x_range=[0, 10], color=BLUE_C, stroke_width=6)
        llm_curve = axes.plot(llm_fn, x_range=[0, 10], color=ORANGE_C, stroke_width=6)

        # labels placed where each curve is clear and they don't overlap
        human_tag = txt("Human-created content", font_size=26, color=BLUE_C)
        human_tag.next_to(axes.c2p(2.3, human_fn(2.3)), UP, buff=0.25)
        llm_tag = txt("AI-generated content", font_size=26, color=ORANGE_C)
        llm_tag.next_to(axes.c2p(8.8, 7.0), UP, buff=0.15)

        # narration: an awkward fact — high-quality human text is running out.
        self.play(Create(human_curve), FadeIn(human_tag), run_time=2.0)
        self.wait(2.0)
        # narration: meanwhile, AI-generated content is exploding exponentially.
        self.play(Create(llm_curve), FadeIn(llm_tag), run_time=2.5)
        self.wait(2.5)

        # crossing point
        ts = np.linspace(0.1, 10, 5000)
        h, l = hook_curves(ts)
        cross_t = float(ts[np.argmin(np.abs(h - l))])
        cross_y = human_fn(cross_t)
        dot = Dot(axes.c2p(cross_t, cross_y), color=RED_C, radius=0.1)
        vline = DashedLine(
            axes.c2p(cross_t, 0), axes.c2p(cross_t, cross_y), color=RED_C, stroke_width=3
        )
        self.play(Create(vline), GrowFromCenter(dot), run_time=1.2)

        # narration: before long, AI content online will overtake human content.
        q = txt("AI content is about to overtake human content", font_size=32, color=RED_C)
        q.to_edge(UP, buff=0.55)
        self.play(FadeOut(title), FadeIn(q, shift=DOWN * 0.2), run_time=1.2)
        self.wait(3.0)

        # narration: so… can we train the next generation of AI on AI-generated data?
        punch = txt("So… can we train AI on AI-generated data?", font_size=32, color=YELLOW)
        punch.to_edge(DOWN, buff=0.45)
        self.play(Write(punch), run_time=2.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 2. Core scene: 1-D Gaussian recursive collapse
# ======================================================================
class GaussianCollapse(Scene):
    def construct(self):
        means, stds = GAUSS_MEANS, GAUSS_STDS
        peak_max = float(np.max(1.0 / (stds * np.sqrt(2 * np.pi))))
        ymax = max(0.5, peak_max * 1.12)

        # narration: let's start with the simplest possible experiment.
        title = txt("Experiment: a Gaussian repeatedly 'learns from itself'", font_size=32, color=WHITE)
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

        # narration: take a standard normal distribution — it represents the real world.
        curve0 = axes.plot(lambda x: gauss_pdf(x, means[0], stds[0]), color=BLUE_C, stroke_width=6)
        real_tag = txt("Real distribution N(0, 1)", font_size=24, color=BLUE_C)
        real_tag.next_to(axes.c2p(0, gauss_pdf(0, 0, 1)), UR, buff=0.1).shift(RIGHT * 0.6)
        self.play(Create(curve0), FadeIn(real_tag), run_time=1.5)
        self.wait(3.5)

        # live readouts in the top-right corner
        gen_label = txt("Gen 0", font_size=28, color=WHITE)
        mu_label = Text("μ = %.2f" % means[0], font=LATIN, font_size=26, color=ORANGE_C)  # ⚡ Text, no latex (MathTex made this scene 2.4x slower)
        sigma_label = Text("σ = %.2f" % stds[0], font=LATIN, font_size=26, color=GREEN_C)
        info = VGroup(gen_label, mu_label, sigma_label).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        info.to_corner(UR, buff=0.5).shift(DOWN * 0.4)
        self.play(FadeIn(info), run_time=0.8)

        # narration: draw 100 samples, fit the next gen from their mean/variance, repeat.
        recipe = txt("Each gen: draw 100 samples → fit a new Gaussian from their mean/variance", font_size=22, color=GREY_C)
        recipe.to_edge(DOWN, buff=0.3)
        self.play(FadeIn(recipe), run_time=0.8)
        self.wait(4.5)

        # key narrative beats: pause at these generations to give the voiceover time
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
            # fade the old curve into a trace
            faded = prev_curve.copy().set_stroke(opacity=0.18, color=GREY_C, width=2.5)
            traces.add(faded)

            new_gen = txt(f"Gen {n}", font_size=28, color=WHITE).move_to(gen_label)
            new_mu = Text("μ = %.2f" % mu, font=LATIN, font_size=26, color=ORANGE_C).move_to(mu_label)
            new_sig = Text("σ = %.2f" % sig, font=LATIN, font_size=26, color=GREEN_C).move_to(sigma_label)

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
        # narration: after twenty gens it has drifted far from N(0,1), and can never go back.
        verdict = txt("The distribution drifts and narrows — never back to N(0,1)", font_size=28, color=RED_C)
        verdict.next_to(recipe, UP, buff=0.25)
        self.play(FadeOut(recipe), FadeIn(verdict), run_time=1.2)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 3. Tail-cutoff scene
# ======================================================================
class TailCutoff(Scene):
    def construct(self):
        # narration: why does this happen? the root cause is one word — sampling.
        title = txt("Why? Rare events simply never get sampled", font_size=32, color=WHITE)
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

        # histogram: discretize N(0,1) into bins
        n_bins = 24
        edges = np.linspace(-4, 4, n_bins + 1)
        centers = 0.5 * (edges[:-1] + edges[1:])
        width = edges[1] - edges[0]
        probs = gauss_pdf(centers, 0, 1)

        M = 100
        threshold = 1.0 / M  # below this density, ~unsampled among 100 samples

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
        # narration: draw the distribution as a histogram; each bar is one event's probability; common in the middle, rare on the sides.
        self.play(LaggedStart(*[GrowFromEdge(b, DOWN) for b in bars], lag_ratio=0.04), run_time=2.0)
        self.wait(4.0)

        # draw the 1/M threshold line
        thr_line = DashedLine(
            axes.c2p(-4, threshold), axes.c2p(4, threshold), color=YELLOW, stroke_width=3
        )
        thr_label = MathTex(r"p < \tfrac{1}{M} = \tfrac{1}{100}", font_size=32, color=YELLOW)
        thr_label.next_to(axes.c2p(4, threshold), UP, buff=0.1).shift(LEFT * 1.6)
        self.play(Create(thr_line), FadeIn(thr_label), run_time=1.2)

        # all narration text goes in the top whitespace band under the title, clear of the x-axis ticks
        text_anchor = title.get_bottom() + DOWN * 0.35
        explain = txt("Only M=100 samples → events with prob < 1/M appear < 1 time in expectation",
                      font_size=22, color=GREY_C)
        explain.move_to([0, text_anchor[1], 0])
        # narration: with only 100 samples, sub-1/M events are expected less than once — basically never sampled.
        self.play(FadeIn(explain), run_time=1.0)
        self.wait(5.0)

        # cut the tail bins (below threshold)
        tail_bars = [b for b, p in zip(bars, probs) if p < threshold]
        keep_bars = [b for b, p in zip(bars, probs) if p >= threshold]
        for b in tail_bars:
            b.generate_target()
            b.target.set_fill(RED_C, opacity=0.9)
        # narration: and so these tails are quietly erased.
        self.play(*[MoveToTarget(b) for b in tail_bars], run_time=0.8)
        self.play(
            LaggedStart(*[b.animate.shift(DOWN * 3).set_opacity(0) for b in tail_bars], lag_ratio=0.05),
            run_time=1.4,
        )
        self.wait(3.0)

        # narration: once information is lost, it can never be recovered.
        lost = txt("Tail information is lost — and it's irreversible", font_size=28, color=RED_C)
        lost.move_to(explain)
        self.play(FadeOut(explain), FadeIn(lost), run_time=1.0)
        self.wait(3.0)

        # next gen re-normalizes over the cut distribution -> narrower
        kept_probs = np.array([p for p in probs if p >= threshold])
        kept_centers = np.array([c for c, p in zip(centers, probs) if p >= threshold])
        renorm = kept_probs / (kept_probs.sum() * width)
        # recompute each kept bar's target height (taller/narrower after renorm)
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
        # narration: the next gen re-normalizes over the cut distribution — narrower, shorter tails.
        self.play(*[MoveToTarget(b) for b in keep_bars], run_time=1.4)
        self.wait(1.5)
        narrower = txt("Next gen re-normalizes → narrower, with shorter tails", font_size=24, color=ORANGE_C)
        narrower.move_to(explain)
        self.play(FadeOut(lost), FadeIn(narrower), run_time=1.0)
        # narration: generation after generation, the distribution keeps collapsing toward the center.
        self.wait(4.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 4. GMM two-peak merge
# ======================================================================
class GMMMerge(Scene):
    def gmm_pdf(self, x, w, mu, sig):
        return sum(
            w[k] * gauss_pdf(x, mu[k], sig[k]) for k in range(len(w))
        )

    def construct(self):
        title = txt("Not just Gaussians: two peaks slowly 'entangle' into one", font_size=32, color=WHITE)
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

        # VAE side-note under the title, so it isn't cropped at the bottom
        note = txt("(VAE handwritten digits do the same: more like one 'average digit' — see paper Fig. 9)",
                   font_size=20, color=GREY_C)
        note.next_to(title, DOWN, buff=0.2)

        hist = GMM_HISTORY
        w0, mu0, sig0 = hist[0]
        # narration: this isn't just about Gaussians. switch to a two-peak mixture…
        curve = axes.plot(lambda x: self.gmm_pdf(x, w0, mu0, sig0), color=BLUE_C, stroke_width=6)
        tag = txt("Real distribution: two clear peaks", font_size=24, color=BLUE_C).to_edge(DOWN, buff=0.45)
        self.play(Create(curve), FadeIn(tag), FadeIn(note), run_time=1.2)

        gen_label = txt("Gen 0", font_size=28, color=WHITE).to_corner(UR, buff=0.6).shift(DOWN * 0.6)
        self.play(FadeIn(gen_label))
        self.wait(3.0)

        # narration: the same process pulls the two peaks together and entangles them.
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
            new_gen = txt(f"Gen {n}", font_size=28, color=WHITE).move_to(gen_label)
            self.play(
                Transform(curve, new_curve),
                Transform(gen_label, new_gen),
                run_time=1.05,
            )
            if n in pauses:
                self.wait(pauses[n])

        # narration: finally collapses into one peak. VAE digits look more like one 'average digit'.
        verdict = txt("Modes entangle → finally collapse into one peak", font_size=28, color=RED_C).move_to(tag)
        self.play(FadeOut(tag), FadeIn(verdict), run_time=1.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 5. Real LLM text comparison (OPT-125m)
# ======================================================================
class LLMTextScene(Scene):
    def construct(self):
        # narration: what about a real LLM? it doesn't escape either.
        title = txt("Real LLMs don't escape either: OPT-125m, 9 generations", font_size=32, color=WHITE)
        title.to_edge(UP, buff=0.4)
        self.play(FadeIn(title), run_time=0.8)
        self.wait(2.5)

        # narration: researchers took OPT-125m and fine-tuned it on its own text, nine generations over.
        prompt = txt(
            "Input (a Wikipedia passage on English parish church towers)…",
            font_size=22,
            color=GREY_C,
        ).next_to(title, DOWN, buff=0.35)
        self.play(FadeIn(prompt), run_time=0.6)
        self.wait(3.5)

        def make_row(gen, text, color, highlight=None):
            tag = txt(gen, font_size=24, color=color, weight=BOLD)
            body = Text(
                text,
                font=LATIN,
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

        # narration per gen: Gen0 fine / Gen1 mixes things up / Gen7 drifts off-topic / Gen9 confident nonsense
        row_holds = [4.5, 4.5, 5.0, 7.0]
        for r, hold in zip(rows, row_holds):
            self.play(FadeIn(r, shift=RIGHT * 0.2), run_time=1.1)
            self.wait(hold)

        # narration: this is what model collapse looks like on a real language model.
        punch = txt("By Gen 9, confidently talking nonsense", font_size=28, color=RED_C)
        punch.to_edge(DOWN, buff=0.4)
        self.play(FadeIn(punch, shift=UP * 0.2), run_time=1.0)
        self.wait(4.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.0)


# ======================================================================
# 6. Conclusion
# ======================================================================
class ConclusionScene(Scene):
    def construct(self):
        l1 = txt("Model collapse is the fate of every generative model.", font_size=38, color=WHITE)
        l2 = txt("Provable mathematically: this drift is inevitable — not a bug, a destiny.", font_size=26, color=GREY_C)
        top = VGroup(l1, l2).arrange(DOWN, buff=0.35).shift(UP * 1.2)
        # narration: model collapse is the shared fate of all generative models.
        self.play(FadeIn(l1, shift=UP * 0.2), run_time=1.2)
        self.wait(2.0)
        # narration: provable mathematically — this drift is inevitable. not a bug, a destiny.
        self.play(FadeIn(l2), run_time=1.0)
        self.wait(3.0)

        # narration: so human-made data, unpolluted by AI, only grows more valuable.
        punch1 = txt("So human-made data, unpolluted by AI,", font_size=34, color=YELLOW)
        punch2 = txt("will only grow more valuable.", font_size=44, color=YELLOW, weight=BOLD)
        bottom = VGroup(punch1, punch2).arrange(DOWN, buff=0.3).shift(DOWN * 1.0)
        self.play(Write(punch1), run_time=1.4)
        self.play(FadeIn(punch2, scale=1.15), run_time=1.2)
        self.wait(3.5)

        # narration: every original thing you post now is quietly appreciating.
        last = txt("Every original thing you post now is appreciating.", font_size=28, color=WHITE)
        last.to_edge(DOWN, buff=0.6)
        self.play(FadeIn(last, shift=UP * 0.2), run_time=1.2)
        self.wait(5.0)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.2)


# ======================================================================
# 7. References
# ======================================================================
class ReferencesScene(Scene):
    def construct(self):
        title = txt("References", font_size=40, color=WHITE).to_edge(UP, buff=1.0)
        self.play(FadeIn(title, shift=DOWN * 0.2), run_time=1.0)

        authors = Text(
            "Ilia Shumailov · Zakhar Shumaylov · Yiren Zhao\n"
            "Yarin Gal · Nicolas Papernot · Ross Anderson",
            font=LATIN, font_size=24, color="#c9d1d9", line_spacing=1.1,
        )
        paper = Text(
            "The Curse of Recursion:\nTraining on Generated Data Makes Models Forget",
            font=LATIN, font_size=30, color=BLUE_C, line_spacing=1.1, weight=BOLD,
        )
        arxiv = Text("arXiv:2305.17493  (2024)", font=LATIN, font_size=26, color=ORANGE_C)
        block = VGroup(authors, paper, arxiv).arrange(DOWN, buff=0.5).move_to(ORIGIN)
        self.play(FadeIn(authors), run_time=0.8)
        self.play(Write(paper), run_time=1.6)
        self.play(FadeIn(arxiv, shift=UP * 0.1), run_time=0.8)

        note = txt("The OPT-125m text (Gen 0/1/7/9) and the VAE Fig. 9 in this video are from that paper",
                   font_size=20, color=GREY_C).to_edge(DOWN, buff=0.9)
        self.play(FadeIn(note), run_time=0.8)
        self.wait(3.5)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.2)
