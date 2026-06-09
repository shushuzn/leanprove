# leanprove

Lean 4 数学形式化证明项目 — 从素数分布到黎曼猜想的探索之旅。

## 项目概述

使用 [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4/) 对数论定理进行严格的形式化证明。项目从素数的模运算性质出发，逐步推进到解析数论的核心结果。

**当前进度**: 阶段 3 / 6 — 已完成素数分布基础、Chebyshev 理论与等差数列素数特殊情形

## 路线图

```
阶段 1 ████████████ 素数分布基础              ✅ 完成
阶段 2 ████████████ Chebyshev 理论            ✅ 完成
阶段 3 ██████░░░░░░ 等差数列中的素数           🔶 部分完成
阶段 4 ░░░░░░░░░░░░ 素数定理                  待开始
阶段 5 ░░░░░░░░░░░░ ζ 函数与零点              待开始
阶段 6 ░░░░░░░░░░░░ 黎曼猜想                  待开始
```

### 阶段 1: 素数分布基础 ✅

围绕 `24 | p² - 1` (p ≥ 5 素数) 的原创证明体系, 涵盖模运算、整除性与推广。

| 定理 | 陈述 | 文件 |
|------|------|------|
| `prime_ge_five_mod_six` | p ≥ 5 素数 → p ≡ 1 或 5 (mod 6) | Basic |
| `prime_ge_five_sq_sub_one_dvd` | 24 \| p² - 1 | Basic |
| `prime_sq_diff_dvd_24` | 24 \| p² - q² | Basic |
| `gcd_pm1_eq_two` | gcd(p-1, p+1) = 2 | Basic |
| `lcm_pm1_eq_half_mul` | lcm(p-1, p+1) = (p-1)(p+1)/2 | Basic |
| `prime_sq_mod_twelve` | p² ≡ 1 (mod 12) | Basic |
| `prime_sq_sum_mod_24` | p² + q² ≡ 2 (mod 24) | Basic |
| `odd_not_three_sq_sub_one_dvd` | 24 \| n² - 1 (奇数, 3∤n) | Basic |
| `odd_not_three_cubed_sub_self_dvd` | 24 \| n³ - n | Basic |
| `odd_not_three_fourth_sub_one_dvd` | 48 \| n⁴ - 1 | Basic |

### 阶段 2: Chebyshev 理论 ✅

Chebyshev 函数的性质、素数计数函数的上下界, 以及 Bertrand 假设的应用。

| 主题 | 内容 | 文件 |
|------|------|------|
| Chebyshev 函数 | θ(x), ψ(x) 的定义、性质与传递链 | Chebyshev |
| π(x) 上界 | π(x) ≤ ln4·x/ln√x + √x | Chebyshev |
| π(x) 下界 | ((x-1)ln2 - ln(x+2))/lnx ≤ π(x) | Chebyshev |
| Bertrand 假设 | ∃p 素数: n < p ≤ 2n | Bertrand |
| 素数无穷性 | ∀N, ∃p > N, p 素数 | Bertrand |
| 素数倒数发散 | Σ 1/p 不收敛 | PrimeReciprocals |

### 阶段 3: 等差数列中的素数 🔶

Dirichlet 定理 (1837) 的特殊情形: 用初等方法证明特定等差数列中包含无穷多个素数。

| 定理 | 方法 | 文件 |
|------|------|------|
| p ≡ 1 (mod 4) 素数无穷多 | Mathlib 分圆多项式方法 | Dirichlet |
| p ≡ 3 (mod 4) 素数无穷多 | **原创**: 欧几里得式构造 N = 4P - 1 | Dirichlet |
| ≡ 3 (mod 4) 的数有 ≡ 3 (mod 4) 素因子 | **原创**: primeFactorsList 论证 | Dirichlet |

**重要发现**: Mathlib 已包含完整的 Dirichlet 定理
(`Nat.forall_exists_prime_gt_and_modEq`, 在 `Mathlib.NumberTheory.LSeries.PrimesInAP` 中)。
本文件的价值在于: p ≡ 3 (mod 4) 的证明是原创的初等方法, 与 Mathlib 的解析证明互补。

### 阶段 4-6: 待实现

| 阶段 | 主题 | 核心目标 | Mathlib 现状 |
|------|------|----------|-------------|
| 4 | 素数定理 | π(x) ~ x/ln(x) | 缺少 ζ 解析延拓、Tauber 定理 |
| 5 | ζ 函数与零点 | 非平凡零点的分布 | 缺少函数方程、Hadamard 乘积 |
| 6 | 黎曼猜想 | 零点在 Re(s) = 1/2 上 | 未解决 (千禧年问题) |

## 项目结构

```
leanprove/
├── Leanprove.lean              # 入口文件
├── Leanprove/
│   ├── Basic.lean              # 核心数论定理 (25 个定理)
│   ├── Bertrand.lean           # Bertrand 假设及其应用 (6 个定理)
│   ├── Chebyshev.lean          # Chebyshev 函数与界限 (16 个定理)
│   ├── Dirichlet.lean          # 等差数列素数特殊情形 (6 个定理)
│   ├── PrimeCounting.lean      # 素数计数函数与 PNT 目标 (3 个定理)
│   ├── PrimeReciprocals.lean   # 素数倒数和发散性 (1 个定理)
│   └── MathlibTest.lean        # Mathlib 功能验证 (1 个定理)
├── ARCHITECTURE.txt            # 定理依赖架构图
├── ROADMAP.md                  # 详细路线图与发展建议
├── lakefile.toml               # 构建配置
├── lean-toolchain              # Lean 版本锁定
└── README.md                   # 本文件
```

**总计**: 58 个已证明定理, 零 sorry

## 技术栈

| 组件 | 版本 | 说明 |
|------|------|------|
| Lean 4 | v4.31.0-rc2 | 证明助手与编程语言 |
| Mathlib | v4.31.0-rc2 | 社区数学库 |
| Lake | — | 构建系统 |

**证明策略**: `omega`, `ring_nf`, `simp`, `decide`, `norm_num`, `linarith`, `rcases`, `by_contra`

## 构建

```bash
lake build Leanprove
```

需要 Lean 4 和 Mathlib 依赖。首次构建会下载并编译 Mathlib (约 3200 个模块)。

## 参考文献

1. Hardy & Wright, *An Introduction to the Theory of Numbers*
2. Apostol, *Introduction to Analytic Number Theory*
3. Davenport, *Multiplicative Number Theory*
4. Iwaniec & Kowalski, *Analytic Number Theory*
5. Aigner & Ziegler, *Proofs from THE BOOK*
6. [Lean 4 Mathlib](https://leanprover-community.github.io/mathlib4/)
7. [Riemann Hypothesis — Clay Mathematics Institute](https://www.claymath.org/millennium-problems/riemann-hypothesis/)

## 许可证

本项目中的数学证明是人类知识的共同财富。
