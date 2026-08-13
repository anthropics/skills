"""
Per-paper file: the narration script. Order matches pipeline_config.SCENES one-to-one.
NARRATION[i] is the list of sentences for scene i (pauses are inserted between sentences).
SCENE_RATES[i] speeds up an individual scene (edge-tts --rate) so the audio fits the on-screen time.

(Below is the "model collapse" example; replace it wholesale per paper.)
"""

SCENE_RATES = {3: "+8%", 6: "+8%"}  # scenes 3 (Tail) / 6 (Conclusion) run a bit long

NARRATION = [
    # 0. IntroScene
    [
        "Let me introduce the paper we're reading today.",
        "Published in 2024, it's titled: The Curse of Recursion — Training on Generated Data Makes Models Forget.",
        "The authors are from Oxford, Cambridge, Imperial College, and others.",
        "Without further ado, let's read this paper together.",
    ],
    # 1. HookScene
    [
        "Training a large model like GPT takes a massive amount of human text.",
        "But here's an awkward fact: high-quality human text is running out.",
        "At the same time, AI-generated content is exploding exponentially.",
        "Before long, AI-generated content online will outnumber human content.",
        "Which raises a tempting idea: could we train the next generation of AI on AI-generated data?",
    ],
    # 2. GaussianCollapse
    [
        "Let's start with the simplest possible experiment.",
        "Take a standard normal distribution — this blue bell curve — representing the real world.",
        "Now let it reproduce itself: draw a hundred samples from the current distribution,",
        "then fit the next generation using the mean and variance of those samples.",
        "Then sample from the new distribution, fit again, and repeat.",
        "Watch the top right — each generation's mean and standard deviation are quietly shifting.",
        "The mean drifts, the variance shrinks, the distribution gets narrower and narrower.",
        "After twenty generations, it has drifted far from the original standard normal,",
        "and it can never go back.",
    ],
    # 3. TailCutoff
    [
        "Why does this happen? The root cause is one word: sampling.",
        "Draw the distribution as a histogram — each bar is the probability of one possible event.",
        "Tall bars in the middle are common events; short bars on the sides are rare events.",
        "When you draw only a hundred samples, an event with probability below one percent",
        "is expected to appear less than once — so most likely, you never sample it at all.",
        "And so these tails are quietly erased.",
        "Once information is lost, it can never be recovered.",
        "The next generation re-normalizes over the cut distribution, so it gets narrower, with shorter tails.",
        "Generation after generation, the distribution keeps collapsing toward the center.",
    ],
    # 4. GMMMerge
    [
        "And this isn't just about Gaussians.",
        "Switch to a two-peak mixture, and the same process pulls the two peaks together,",
        "entangling them, until they collapse into a single peak.",
        "The handwritten digits from a variational autoencoder do the same thing —",
        "looking more and more like one blurry, average digit.",
    ],
    # 5. LLMTextScene
    [
        "So what about a real large language model? It doesn't escape either.",
        "Researchers took a small model called OPT and fine-tuned it on its own generated text, nine generations over.",
        "Generation zero still looks normal — it talks about architectural history.",
        "Generation one starts mixing things up, but the sentences are still coherent.",
        "By generation seven, it has drifted off into interviews and small talk.",
        "And by generation nine, it's confidently talking nonsense:",
        "black-tailed, white-tailed, blue-tailed, red-tailed jackrabbits — a long list of things that don't exist.",
        "This is what model collapse looks like on a real language model.",
    ],
    # 6. ConclusionScene
    [
        "Model collapse is the shared fate of all generative models.",
        "It can be proven mathematically — this drift is inevitable. Not a bug, but a destiny.",
        "So data that hasn't been polluted by AI — genuinely created by humans —",
        "will only become more valuable.",
        "In other words, every original thing you post online right now is quietly appreciating.",
    ],
    # 7. ReferencesScene (end-card; empty = silent card)
    [],
]
