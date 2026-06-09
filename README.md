# leanprove

Lean 4 数学形式化证明项目 — 从素数分布到黎曼猜想的探索之旅。

## 项目概述

使用 [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4/) 对数论定理进行严格的形式化证明。项目从素数的模运算性质出发，逐步推进到解析数论的核心结果。

**当前进度**: 阶段 IV-A / VI — Zeta 函数基础 (已完成) → 阶段 IV-B (进行中)

**注**: 全项目共 **93+ 个定理/引理**, 涵盖初等数论、Chebyshev 理论、Dirichlet 定理、Von Mangoldt 函数、Mertens 第一定理和 ζ 函数基础。

## 路线图

```
阶段 I   ████████████ 初等数论基础                ✅ 完成
阶段 II  ████████████ Chebyshev 与素数分布         ✅ 完成
阶段 III ████████████ 解析数论基础                 ✅ 完成
阶段 IV  ████░░░░░░░░ Zeta 函数系列               🔶 进行中
  IV-A  ████████████ ζ(s) 定义与绝对收敛           ✅ 完成
  IV-B  ████░░░░░░░░ 极点: (s-1)ζ(s) → 1           🔶 进行中
  IV-C  ░░░░░░░░░░░░ Euler 乘积                   待开始
  IV-D  ░░░░░░░░░░░░ 解析延拓与零区域             待开始
阶段 V  ░░░░░░░░░░░░ 素数定理 (PNT)              待开始
阶段 VI ░░░░░░░░░░░░ 黎猜想                      待开始
```

---

### 阶段 I: 初等数论基础 ✅

**文件**: `Basic.lean`, `PrimeCounting.lean`, `PrimeReciprocals.lean`

素数模运算性质、素数无穷性与素数计数的基本估计。

| # | 定理 | 方法 |
|---|------|------|
| 1 | `24 | p² - 1` 对素数 p ≥ 5 | 模 3 和模 8 分析 |
| 2 | `24 | p² - q²` 对素数 p,q ≥ 5 | 平方差公式 |
| 3 | `48 | n⁴ - 1` 对奇数 n, 3 ∤ n | 因式分解 |
| 4 | 素数无穷 | 欧几里得经典证明 |
| 5 | `π(x) < x/ln x · ln 4 + O(√x)` | 组合上界 |
| 6 | `Σ 1/p` 发散 | 厄多斯证明 |
| 7 | 素数计数上界 | `π(x) ≤ 1.25506·x/ln x` |
| 8 | Chebyshev 下界 | `π(x) > x/ln x` 对 x ≥ 17 |

**关键定理**: 24 | p² - 1 的完整证明体系 (模 3 + 模 8 + 分类讨论 + 7 种推广)

---

### 阶段 II: Chebyshev 与素数分布 ✅

**文件**: `Chebyshev.lean`, `Bertrand.lean`, `PrimeReciprocals.lean`

Chebyshev θ(x) 和 ψ(x) 函数、Bertrand 假设、素数计数函数的上下界。

| # | 定理 | 方法 |
|---|------|------|
| 1 | θ(x) = Σ_{p≤x} ln p 定义与性质 | 传递链构造 |
| 2 | ψ(x) = Σ_{p^k ≤ x} ln p | Von Mangoldt 函数 |
| 3 | θ(x) ≥ x·ln 2 - ln(x+1) | 乘积下界 |
| 4 | ψ(x) ≤ (ln 4 + 4)x | 组合上界 |
| 5 | **Bertrand 假设**: ∃ p: n < p ≤ 2n | 中心二项式系数 |
| 6 | |ψ(x) - θ(x)| ≤ 2√x·ln x | 素数幂贡献 |
| 7 | π(x) > x/ln x (x ≥ 17) | Chebyshev 下界 |
| 8 | π(x) < 1.25506·x/ln x | Rosser 上界 |

**关键定理**: Chebyshev 界 ψ(x) = O(x), θ(x) ~ x, Bertrand 假设

---

### 阶段 III: 解析数论基础 ✅

**文件**: `Dirichlet.lean`, `VonMangoldt.lean`

等差数列中的素数、Von Mangoldt 函数、Mertens 第一定理、Stirling 公式。

| # | 定理 | 方法 |
|---|------|------|
| 1 | p ≡ 1 (mod 4) 素数无穷 | n²+1 素因子法 (原创) |
| 2 | p ≡ 3 (mod 4) 素数无穷 | 欧几里得构造 M = 4P - 1 (原创) |
| 3 | p ≡ 5 (mod 6) 素数无穷 | 欧几里得构造 M = 6P - 1 (原创) |
| 4 | Λ(n) 定义与 Dirichlet 卷积 | ∑_{d|n} Λ(d) = ln n |
| 5 | ψ(x) = ∑_{n≤x} Λ(n) | Chebyshev psi |
| 6 | **Mertens 恒等式**: ∑ Λ(n)/n = ψ/x + ∫ ψ/t² dt | Abel 求和公式 |
| 7 | **素数幂贡献有界** | 几何级数界 |
| 8 | ∑ ln n = N·ln N - N + O(ln N) | **Stirling 公式** (积分比较) |
| 9 | **卷积恒等式**: ∑ Λ(n)·⌊N/n⌋ = ∑ ln k | 除数双射 |
| 10 | **Mertens 第一定理**: ∑ Λ(n)/n = ln x + O(1) | Stirling + Chebyshev |
| 11 | ∫ ψ/t² dt - ln x = O(1) | Mertens + Abel 恒等式 |

**关键定理**: Mertens 第一定理 (全程初等证明, 无需素数定理)

---

### 阶段 IV: Zeta 函数系列 🔶

**文件**: `Zeta.lean`

Riemann ζ 函数的分阶段构建。每个子阶段独立可验证。

#### IV-A: ζ(s) 定义与绝对收敛 ✅

| # | 定理 | 状态 |
|---|------|------|
| 1 | ζ(s) = ∑ 1/n^s (Re s > 1) | ✅ |
| 2 | ∑ |1/n^s| 收敛 (Re s > 1) | ✅ |
| 3 | |ζ(s)| ≤ ζ(Re(s)) | ✅ |

#### IV-B: 极点 (s-1)ζ(s) → 1 🔶

| # | 定理 | 方法 |
|---|------|------|
| 1 | ∫_1^N x^{-σ} dx = (N^{1-σ} - 1)/(1-σ) | integral_rpow |
| 2 | 1/(σ-1) ≤ ζ(σ) ≤ 1 + 1/(σ-1) | 积分比较 |
| 3 | (σ-1)ζ(σ) → 1 当 σ → 1⁺ | squeeze 定理 |

#### IV-C: Euler 乘积 ⏳

| # | 定理 |
|---|------|
| 1 | ζ(s) = ∏_p (1 - p^{-s})⁻¹ (Re s > 1) |

#### IV-D: 解析延拓与零区域 ⏳

| # | 定理 |
|---|------|
| 1 | ζ(s) - 1/(s-1) 解析延拓到 Re s ≥ 1 |
| 2 | ζ(s) ≠ 0 对 Re s ≥ 1 |

---

### 阶段 V: 素数定理 (PNT) ⏳

| # | 定理 |
|---|------|
| 1 | ψ(x) ∼ x (等价于 π(x) ∼ x/ln x) |
| 2 | ∑_{n≤x} Λ(n) = x + o(x) |
| 3 | ∑_{p≤x} ln p ∼ x |
| 4 | p_n ∼ n·ln n |

**方法**: Newman 证明路径 (复分析 + Tauberian)

---

### 阶段 VI: 黎曼猜想 ⏳

| # | 定理 |
|---|------|
| 1 | ζ(s) 的函数方程 |
| 2 | ζ(s) 的零点分布 |
| 3 | 黎曼假设: 所有非平凡零点位于 Re(s) = 1/2 |
| 4 | 素数定理的误差项改进 |

---

## 项目结构

```
leanprove/
├── Leanprove.lean              # 入口文件
├── Leanprove/
│   ├── Basic.lean              # 阶段 I: 21 定理
│   ├── Chebyshev.lean          # 阶段 II: 14 定理
│   ├── Bertrand.lean           # 阶段 II: 6 定理
│   ├── PrimeCounting.lean      # 阶段 I-II: 3 定理
│   ├── PrimeReciprocals.lean   # 阶段 I: 1 定理
│   ├── Dirichlet.lean          # 阶段 III: 11 定理
│   ├── VonMangoldt.lean        # 阶段 III: 36 定理/引理
│   ├── Zeta.lean               # 阶段 IV: ζ 函数基础
│   └── Tests.lean              # 测试与验证
├── ROADMAP.md                  # 详细路线图与发展建议
├── lakefile.toml               # 构建配置
├── lean-toolchain              # Lean 版本锁定
└── README.md                   # 本文件
```

**总计**: 93 个已证明定理/引理, 零 sorry (Zeta.lean 另有 5 个进行中的定理)

## 技术栈

| 组件 | 版本 | 说明 |
|------|------|------|
| Lean 4 | v4.31.0-rc2 | 证明助手与编程语言 |
| Mathlib | v4.31.0-rc2 | 社区数学库 |
| Lake | — | 构建系统 |

## 构建

```bash
lake build              # 构建全部
lake build Leanprove    # 构建主入口
lean --run <file>       # 运行单个文件
```
