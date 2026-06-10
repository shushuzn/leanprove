## leanprove 项目路线图

本文档是 leanprove 项目的前瞻性规划。项目现状与已完成定理清单见 [README.md](README.md)。

---

### 项目总览

```
阶段 I   ████████████ 初等数论基础                ✅ 完成
阶段 II  ████████████ Chebyshev 与素数分布         ✅ 完成
阶段 III ████████████ 解析数论基础                 ✅ 完成
阶段 IV  ██████░░░░░░ Zeta 函数系列               🔶 进行中
  IV-A  ████████████ ζ(s) 定义与绝对收敛           ✅ 完成
  IV-B  ████████████ (σ-1)ζ(σ) 上界               ✅ 完成
  IV-C  ███░░░░░░░░░ Mertens + Abel 求和          🔶 进行中 (4 sorry)
  IV-D  ░░░░░░░░░░░░ Euler 乘积                   待开始
  IV-E  ░░░░░░░░░░░░ 解析延拓与零区域             待开始
阶段 V  ░░░░░░░░░░░░ 素数定理 (PNT)              待开始
阶段 VI ░░░░░░░░░░░░ 黎曼猜想                    待开始
```

---

### Mathlib 中已有的关键结果

在推进后续阶段前, 了解 Mathlib 中已有的成果至关重要:

**Dirichlet 定理 (完整)**: `Mathlib.NumberTheory.LSeries.PrimesInAP` 中已证明完整的 Dirichlet 定理。

**Chebyshev 函数**: Mathlib 有完整的 θ(x)、ψ(x) 定义, 以及 Chebyshev 界。

**Von Mangoldt 函数**: Mathlib 有 `ArithmeticFunction.vonMangoldt`, 含完整的 Dirichlet 卷积性质。

**尚未在 Mathlib 中形式化的关键结果** (阶段 4-6 所需):

- ζ 函数的解析延拓 (仅有 Re(s) > 1 的定义)
- ζ(1+it) ≠ 0 (PNT 的关键步骤)
- PNT 本身 (π(x) ~ x/ln(x))
- ζ 函数的函数方程
- 零点计数函数 N(T) 和 Hadamard 乘积
- 黎曼猜想的任何非平凡结果

---

### 当前重点: 阶段 IV-C (Mertens + Abel 求和)

**文件**: `VonMangoldt.lean`

**已完成的引理** (全部 sorry-free):

| # | 引理 | 状态 | 用途 |
|---|------|------|------|
| 1 | `vm_nonneg` — Λ(n)/n ≥ 0 | ✅ | 非负性 |
| 2 | `vm_le_one` — Λ(n)/n ≤ 1 (n≥2) | ✅ | 逐项上界 |
| 3 | `pow_div_pow_bound` — 1/p^k ≤ (1/2)^{k-2}·1/p^2 | ✅ | 几何级数分解 |
| 4 | `geom_sum_bound` — ∑_{j=0}^N (1/2)^j ≤ 2 | ✅ | 几何级数上界 |
| 5 | `geom_tail_Icc_bound` — ∑_{k=2}^M 1/p^k ≤ 2/p^2 | ✅ | 素数幂尾部界 |
| 6 | `range_sum_le_tsum_of_nonneg` — 部分和 ≤ tsum | ✅ | tsum 界定 |
| 7 | `log_lt_two_sqrt` — log p < 2√p | ✅ | 对数上界 |
| 8 | `sqrt_div_sq_eq_rpow` — √p/p² = p^{-3/2} | ✅ | 幂函数转换 |
| 9 | `log_div_sq_bound_le` — log p/p² ≤ 2p^{-3/2} | ✅ | 素数对数界 |

**剩余 4 个 sorry**:

| # | 定理 | 技术路线 | 难度 |
|---|------|----------|------|
| 10 | `primePower_contribution_bounded` | ✅ 双重求和法: H(m,j) + Finset.sum_bij + Summable.sum_le_tsum | ✅ |
| 11 | `psi_integral_sub_log_isBigO` | Mertens 第一定理 + Abel 求和公式 | 高 |
| 12 | `mertens_abel_identity` | Abel 求和公式应用于 von Mangoldt 函数 | 高 |
| 13 | `mertens_first_theorem` | ∑_{p≤x} (log p)/p = log x + O(1) | 高 |
| 14 | `mertens_first_theorem_bounded` | 有界形式 \|∑ - log x\| ≤ C | 中 |

**技术细节**:
- `primePower_contribution_bounded` ✅: 双重求和法。定义 H(m,j) = if m prime then (log m)/m^(j+2) else 0，证明 Summable H (summable_prod_of_nonneg + summable_nat_rpow 比较)。注入 f(n) = (n.minFac, n.factorization n.minFac - 2)，用 Finset.sum_bij + Summable.sum_le_tsum 控制部分和。
- `psi_integral_sub_log_isBigO`: 需要 Abel 求和恒等式: ∫ψ(t)/t² dt - log x = ψ(x)/x + ∫(∑Λ(n)/n - ψ(t)/t)/t dt。结合 Mertens 第一定理 ∑Λ(n)/n - log x = O(1) 得到结论。

---

### 已完成阶段详情

#### 阶段 I: 初等数论基础 ✅

**文件**: `Basic.lean`, `PrimeCounting.lean`, `PrimeReciprocals.lean`

21 个定理, 涵盖: 24 | p²-1 的完整证明体系、素数无穷、素数计数上界、Σ 1/p 发散。

#### 阶段 II: Chebyshev 与素数分布 ✅

**文件**: `Chebyshev.lean`, `Bertrand.lean`

14+ 个定理, 涵盖: Chebyshev θ/ψ 函数、Bertrand 假设、素数计数上下界。

#### 阶段 III: 解析数论基础 ✅

**文件**: `Dirichlet.lean`, `VonMangoldt.lean`

11+ 个定理, 涵盖: 等差数列素数、Von Mangoldt 函数、Mertens 第一定理、Stirling 公式。

#### 阶段 IV-A/B: ζ 函数基础 ✅

**文件**: `ZetaIVB.lean`

5 个引理, 全部 sorry-free: rpow_anti, mvt_ineq, n_pow_le_telescope, sum_bound_upper, **zeta_upper_bound** (ζ(σ) ≤ 1 + 1/(σ-1))。

---

### 后续阶段规划

#### IV-D: Euler 乘积

ζ(s) = ∏_p (1 - p^{-s})⁻¹ (Re s > 1)

**依赖**: Von Mangoldt 函数的 Dirichlet 卷积性质 (已有)。

#### IV-E: 解析延拓与零区域

ζ(s) - 1/(s-1) 解析延拓到 Re s ≥ 1; ζ(s) ≠ 0 对 Re s ≥ 1。

**依赖**: 复分析基础设施 (围道积分、留数定理)。

#### 阶段 V: 素数定理 (PNT)

**方法**: Newman 证明路径 (复分析 + Tauberian)。

**替代策略**: Selberg-Erdős 初等证明 (不使用复分析)。

#### 阶段 VI: 黎曼猜想

**现实评估**: RH 是千禧年问题之一, 至今未解决。可形式化等价表述和已知推论。

---

### 推荐的实施顺序

```
近期 (当前)
  ├── ✅ IV-B: (σ-1)ζ(σ) 上界
  ├── ✅ IV-C: primePower_contribution_bounded (双重求和法)
  ├── 🔶 IV-C: psi_integral_sub_log_isBigO (Abel 求和)
  ├── 🔶 IV-C: mertens_abel_identity (Abel 求和恒等式)
  ├── 🔶 IV-C: mertens_first_theorem (Mertens 第一定理)
  └── 🔶 IV-C: mertens_first_theorem_bounded (有界形式)

中期
  ├── IV-D: Euler 乘积
  ├── IV-E: 解析延拓 (需要复分析基础设施)
  └── 向 Mathlib 贡献围道积分、留数定理

远期
  ├── 阶段 V: 素数定理 (PNT)
  ├── 阶段 VI: ζ 函数零点理论
  └── 阶段 VI: 黎曼猜想 (陈述与已知结果)
```

---

### 对 Mathlib 社区的建议

阶段 4 以后的工作高度依赖 Mathlib 中尚不存在的基础设施。建议以向 Mathlib 贡献 PR 的方式推进, 特别是复分析工具和 ζ 函数理论。
