"""
模型崩溃科普视频 —— 数据预计算模块

所有随机过程都在这里用固定随机种子算好，scene 里只读取这些数组，
绝不在渲染时跑随机数 —— 保证每次渲染结果完全一致，方便迭代。

运行 `python model_collapse_data.py` 可以打印关键数值，方便检查。
"""

import numpy as np


# ----------------------------------------------------------------------
# 1. 一维高斯递归崩溃:  采样 -> 用样本均值/方差拟合 -> 再采样
# ----------------------------------------------------------------------
def simulate_gaussian_collapse(n_gen=20, M=100, seed=7):
    """
    返回 means[n_gen+1], stds[n_gen+1] (含第 0 代真实分布 N(0,1))。
    每一代: 从 N(mu, sigma) 采 M 个点, 用 MLE(样本均值, 样本标准差) 当作下一代。
    """
    rng = np.random.default_rng(seed)
    mus = [0.0]
    sigmas = [1.0]
    for _ in range(n_gen):
        s = rng.normal(mus[-1], sigmas[-1], size=M)
        mus.append(float(s.mean()))
        sigmas.append(float(s.std()))  # ddof=0, 最大似然估计
    return np.array(mus), np.array(sigmas)


def pick_gaussian_seed(candidates=range(200), n_gen=20, M=100):
    """挑一个视觉上漂移+收缩都明显的种子(均值漂移大 & 方差收缩明显)。"""
    best, best_score = None, -1e9
    for s in candidates:
        mus, sigmas = simulate_gaussian_collapse(n_gen, M, seed=s)
        drift = abs(mus[-1] - mus[0])
        shrink = sigmas[0] - sigmas[-1]
        # 想要漂移明显、方差变小、且过程平滑不要中途爆炸
        score = drift * 1.5 + shrink * 2.0 - 0.0 * sigmas.std()
        if 0.55 < sigmas[-1] < 0.92 and score > best_score:
            best, best_score = s, score
    return best


# ----------------------------------------------------------------------
# 2. 一维 2 分量 GMM 递归: 采样 -> EM 重新拟合 -> 再采样, 两峰逐渐合并
# ----------------------------------------------------------------------
def _em_gmm_1d(x, k=2, iters=60, rng=None):
    """极简 1D GMM EM。返回 (weights, means, stds)。"""
    n = len(x)
    # 初始化: 用分位点放初始均值, 避免随机初始化带来的不确定
    qs = np.quantile(x, np.linspace(0.2, 0.8, k))
    mu = qs.astype(float)
    sigma = np.full(k, x.std() / k + 1e-3)
    w = np.full(k, 1.0 / k)
    for _ in range(iters):
        # E 步
        comp = (
            w[None, :]
            / (np.sqrt(2 * np.pi) * sigma[None, :])
            * np.exp(-0.5 * ((x[:, None] - mu[None, :]) / sigma[None, :]) ** 2)
        )
        denom = comp.sum(axis=1, keepdims=True) + 1e-12
        r = comp / denom  # responsibilities (n, k)
        # M 步
        nk = r.sum(axis=0) + 1e-12
        w = nk / n
        mu = (r * x[:, None]).sum(axis=0) / nk
        var = (r * (x[:, None] - mu[None, :]) ** 2).sum(axis=0) / nk
        sigma = np.sqrt(var + 1e-6)
    return w, mu, sigma


def simulate_gmm_collapse(n_gen=12, M=300, seed=3):
    """
    真实分布: 0.5*N(-2,0.5^2) + 0.5*N(+2,0.5^2)。
    每代从当前 GMM 采 M 点, EM 重新拟合 2 分量, 记录参数。
    返回列表 history[gen] = (w[2], mu[2], sigma[2])。
    """
    rng = np.random.default_rng(seed)
    w = np.array([0.5, 0.5])
    mu = np.array([-2.0, 2.0])
    sigma = np.array([0.5, 0.5])
    history = [(w.copy(), mu.copy(), sigma.copy())]
    for _ in range(n_gen):
        # 从当前 GMM 采样
        comp_choice = rng.random(M) < w[0]
        s = np.where(
            comp_choice,
            rng.normal(mu[0], sigma[0], M),
            rng.normal(mu[1], sigma[1], M),
        )
        w, mu, sigma = _em_gmm_1d(s, k=2, rng=rng)
        # 按均值排序, 保持两个分量顺序稳定(左/右)
        order = np.argsort(mu)
        w, mu, sigma = w[order], mu[order], sigma[order]
        history.append((w.copy(), mu.copy(), sigma.copy()))
    return history


# ----------------------------------------------------------------------
# 2b. GMM 合并「示意」轨迹 (确定性, 非随机)
# ----------------------------------------------------------------------
# 说明: 真实的 EM 重拟合(上面的 simulate_gmm_collapse)动力学非常嘈杂——
# 要么中途出现峰的「瞬移」, 要么 sigma 塌成接近 0 的尖刺, 不适合做 30 秒
# 干净的科普动画。论文里 GMM 部分本身也是定性展示。因此这里用一条确定性
# 的、平滑的示意轨迹来传达「两峰逐代靠拢、最终纠缠成一个」的直觉。
def gmm_merge_schedule(n_gen=12, mu0=2.0, sigma0=0.5):
    """返回 history[gen] = (w[2], mu[2], sigma[2]) 的平滑合并示意。"""
    history = []
    for n in range(n_gen + 1):
        t = n / n_gen
        s = t * t * (3 - 2 * t)  # smoothstep 缓动
        mu_mag = mu0 * (1 - s) + 0.12 * s  # 两峰从 ±2.0 平滑靠拢到 ±0.12
        sig = sigma0 * (1 - s) + 0.62 * s  # 略微变宽, 融成单峰
        w = np.array([0.5, 0.5])
        mu = np.array([-mu_mag, mu_mag])
        sigma = np.array([sig, sig])
        history.append((w, mu, sigma))
    return history


# ----------------------------------------------------------------------
# 3. 钩子曲线: 人类文本量(放缓) vs LLM 输出量(指数), 交叉点
# ----------------------------------------------------------------------
def hook_curves(t):
    """t: numpy array in [0, 10] (代表 2018 -> 2030 左右的相对时间)。
    两条曲线在 t≈6 处相交, 交点 y≈5.4, 居中留出标注空间。"""
    # 人类内容: 接近饱和的对数增长
    human = 1.0 + 5.5 * np.log1p(t) / np.log1p(10)  # 约 1.0 .. 6.5
    # LLM 内容: 起步晚, 指数爆发
    llm = 0.05 * np.exp(0.80 * t)
    return human, llm


# ----------------------------------------------------------------------
# 预计算好的全局数据 (import 时即固定)
# ----------------------------------------------------------------------
GAUSS_SEED = 7
GAUSS_MEANS, GAUSS_STDS = simulate_gaussian_collapse(n_gen=20, M=100, seed=GAUSS_SEED)
GMM_HISTORY = gmm_merge_schedule(n_gen=12)  # 平滑示意轨迹 (见上方说明)
GMM_HISTORY_REAL = simulate_gmm_collapse(n_gen=12, M=300, seed=3)  # 真实 EM, 备用


if __name__ == "__main__":
    print("== Gaussian collapse (seed=%d) ==" % GAUSS_SEED)
    for i, (m, s) in enumerate(zip(GAUSS_MEANS, GAUSS_STDS)):
        print(f"  gen {i:2d}:  mu={m:+.3f}  sigma={s:.3f}")
    print("\n== GMM collapse ==")
    for i, (w, mu, sig) in enumerate(GMM_HISTORY):
        print(
            f"  gen {i:2d}:  mu=({mu[0]:+.2f},{mu[1]:+.2f})  "
            f"sigma=({sig[0]:.2f},{sig[1]:.2f})  w=({w[0]:.2f},{w[1]:.2f})"
        )
    print("\n建议的高斯种子:", pick_gaussian_seed())
