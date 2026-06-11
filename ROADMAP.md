## leanprove 项目路线图

本文档是 leanprove 项目的前瞻性规划。项目现状与已完成定理清单见 [README.md](README.md)。

---

### 项目总览

```
阶段 I   ████████████ 初等数论基础                ✅ 完成
阶段 II  ████████████ Chebyshev 与素数分布         ✅ 完成
阶段 III ████████████ 解析数论基础                 ✅ 完成
阶段 IV  ████████████ Zeta 函数系列               ✅ 完成
  IV-A  ████████████ ζ(s) 定义与绝对收敛           ✅ 完成
  IV-B  ████████████ (σ-1)ζ(σ) 上界               ✅ 完成
  IV-C  ████████████ Mertens + Abel 求和          ✅ 完成 (0 sorry)
  IV-D  ████████████ Euler 乘积                   ✅ 完成 (0 sorry)
  IV-E  ████████████ 解析延拓与零区域             ✅ 完成 (0 sorry)
阶段 V  ▓▓░░░░░░░░░░ 素数定理 (PNT)              进行中
  V-A   ▓▓▓▓▓▓▓▓▓▓▓▓ PNT 等价形式               ✅ 完成 (2 sorry)
  V-B   ▓▓▓▓▓▓▓▓▓▓▓▓ θ~x ↔ π~x/log x           ✅ 完成 (0 sorry)
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

### 当前重点: 阶段 IV-C (Mertens + Abel 求和) ✅ 已完成

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

**全部已证 (0 sorry)**:

| # | 定理 | 技术路线 | 状态 |
|---|------|----------|------|
| 10 | `primePower_contribution_bounded` | ✅ 双重求和法: H(m,j) + Finset.sum_bij + Summable.sum_le_tsum | ✅ |
| 11 | `psi_integral_sub_log_isBigO` | ✅ Abel 求和 + setIntegral_union + integrableOn_of_bounded | ✅ |
| 12 | `mertens_abel_identity` | ✅ sum_mul_eq_sub_integral_mul₁ + deriv_inv' + integral_congr | ✅ |
| 13 | `mertens_first_theorem` | ✅ 由 mertens_first_theorem_bounded 推出 | ✅ |
| 14 | `mertens_first_theorem_bounded` | ✅ vm_div_sum_sub_log_bound + primePower_contribution_bounded + 三角不等式 | ✅ |

**技术细节**:
- `primePower_contribution_bounded` ✅: 双重求和法。定义 H(m,j) = if m prime then (log m)/m^(j+2) else 0，证明 Summable H (summable_prod_of_nonneg + summable_nat_rpow 比较)。注入 f(n) = (n.minFac, n.factorization n.minFac - 2)，用 Finset.sum_bij + Summable.sum_le_tsum 控制部分和。
- `mertens_abel_identity` ✅: 应用 `sum_mul_eq_sub_integral_mul₁` (c = Λ, f(t) = t⁻¹)。可微性由 `fun_prop` + `z ≥ 2 → z ≠ 0` 证明；可积性通过 `deriv_inv'` 展开后用 `ContinuousOn.div` + `ContinuousOn.pow` 证明。积分内用 `congr_fun deriv_inv'` + `Chebyshev.psi_eq_sum_Icc` 简化被积函数。
- `psi_integral_sub_log_isBigO` ✅: 应用 Abel 求和恒等式 (mertens_abel_identity) 将积分拆分为 ∑Λ(n)/n - ψ(x)/x。用 setIntegral_union 将 (1,x] 积分拆为 (1,2] + (2,x]，其中 (1,2] 积分为零 (ψ t = 0 for t < 2)。可积性通过 MeasureTheory.volume.integrableOn_of_bounded + psi_bounded 证明。结合 Mertens 第一定理有界形式与三角不等式得到 O(1) 估计。

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

#### 阶段 IV-D: Euler 乘积 ✅

**文件**: `ZetaIVD.lean`

4 个定理, 全部 sorry-free: riemannZeta_real_pos, riemannZeta_ne_zero_real, euler_product_real_tendsto, **euler_product_real_hasProd** (完整的 Euler 乘积公式)。

#### 阶段 IV-E: 解析延拓与零区域 ✅

**文件**: `ZetaIVE.lean`

16 个包装定理, 全部 sorry-free: zeta_analytic, zeta_differentiable_at/on, zeta_residue_one, completed_zeta₀_functional_equation, completed_zeta₀_entire, completed_zeta_functional_equation, **zeta_functional_equation** (函数方程), **zeta_ne_zero_of_one_le_re** (PNT 关键引理), zeta_trivial_zero, zeta_at_zero/two/four/even/neg_nat。

---

### 当前重点: 阶段 IV-D (Euler 乘积) ✅ 已完成

**文件**: `ZetaIVD.lean`

**已完成的定理** (全部 sorry-free):

| # | 定理 | 状态 | 技术路线 |
|---|------|------|----------|
| 1 | `riemannZeta_real_pos` — ζ(σ) > 0 (σ > 1) | ✅ | riemannZeta_def + tsum_pos |
| 2 | `riemannZeta_ne_zero_real` — ζ(σ) ≠ 0 (σ > 1) | ✅ | ne_of_gt + riemannZeta_real_pos |
| 3 | `euler_product_real_tendsto` — ∏_p (1 - p^{-σ})⁻¹ → ζ(σ) | ✅ | HasProd.tendsto_partialProd |
| 4 | `euler_product_real_hasProd` — Euler 乘积公式 | ✅ | euler_product_real_tendsto + HasProd |

**技术细节**:
- `riemannZeta_real_pos` ✅: ζ(σ) 定义为 ∑ 1/n^σ，所有项为正，故和为正。使用 `tsum_pos` 证明。
- `riemannZeta_ne_zero_real` ✅: 由正性直接推出非零 (`ne_of_gt`)。
- `euler_product_real_tendsto` ✅: 证明部分乘积 ∏_{p≤N} (1 - p^{-σ})⁻¹ 趋于 ζ(σ)。使用 `HasProd.tendsto_partialProd`。
- `euler_product_real_hasProd` ✅: 完整的 Euler 乘积公式，由 `euler_product_real_tendsto` 和 `HasProd` 构造得出。

---

### 后续阶段规划

#### 阶段 IV-E: 解析延拓与零区域 ✅

**文件**: `ZetaIVE.lean`

16 个定理包装 mathlib 的完整 ζ 函数理论:
- 解析延拓: `zeta_analytic`, `zeta_differentiable_at/on`
- 留数: `zeta_residue_one` (Res(ζ,1) = 1)
- 函数方程: `zeta_functional_equation`, `completed_zeta₀_functional_equation`, `completed_zeta₀_entire`
- **非零区域**: `zeta_ne_zero_of_one_le_re` (ζ(s)≠0 对 Re s ≥ 1, PNT 关键引理)
- 平凡零点: `zeta_trivial_zero` (ζ(-2n) = 0)
- 特殊值: `zeta_at_zero` (ζ(0)=-1/2), `zeta_at_two` (ζ(2)=π²/6), `zeta_at_four`, `zeta_at_even`, `zeta_at_neg_nat`

#### 阶段 V: 素数定理 (PNT)

**V-A/V-B: PNT 等价形式** ✅ 已完成 (2 sorry)

**文件**: `PNTVA.lean`

已证:
- `two_log_div_sqrt_tendsto_zero`: 2·log x / √x → 0 (isLittleO + tendsto_div_nhds_zero)
- `psi_sub_theta_div_x_tendsto_zero`: (ψ-θ)/x → 0 (Chebyshev 界 + 夹逼定理)
- `psi_div_x_iff_theta_div_x`: ψ/x→1 ↔ θ/x→1
- `isEquivalent_id_iff_tendsto_div_one`: u~id ↔ u/x→1
- `pnt_psi_iff_pnt_theta`: ψ~x ↔ θ~x
- `x_div_log_sq_isLittleO_x_div_log`: x/log²x =o(x/log x) (V-B 辅助)
- `pi_isEquivalent_theta_div_log`: π~θ/log (V-B 核心引理, Abel 求和 + Chebyshev 下界)
- `pnt_theta_iff_pnt_pi`: θ~x ↔ π~x/log x (V-B, 由上述引理传递)
- `pnt_psi_iff_pnt_pi`: ψ~x ↔ π~x/log x (传递性)
- `log_deriv_zeta_eq_vonMangoldt_series`: -ζ'/ζ = ∑Λ/n^s (包装 mathlib)
- `log_deriv_zeta_analytic`: -ζ'/ζ 全纯 (analyticOn_riemannZeta.deriv.div + ζ≠0)

待证 (sorry):
- `prime_number_theorem_psi`: ψ~x (需 Tauberian 定理)
- `prime_number_theorem_pi`: π~x/log x (需 Tauberian 定理)

**后续路径**: Newman 证明 (Wiener-Ikehara Tauberian) 或 Selberg-Erdős 初等证明。

#### 阶段 VI: 黎曼猜想

**现实评估**: RH 是千禧年问题之一, 至今未解决。可形式化等价表述和已知推论。

---

### 推荐的实施顺序

```
近期 (当前)
  ├── ✅ IV-E: zeta_ne_zero_of_one_le_re (ζ(s)≠0 on Re s ≥ 1, PNT 关键)
  ├── ✅ IV-E: zeta_functional_equation (函数方程)
  ├── ✅ IV-E: 16 个包装定理 (解析延拓 + 特殊值 + 平凡零点)
  ├── ✅ V-A: PNT 等价形式 (ψ~x ↔ θ~x, 夹逼定理, 5 定理已证)
  └── ✅ V-B: θ~x ↔ π~x/log x (Abel 求和 + Chebyshev 下界 + IsEquivalent 传递)

中期
  ├── V-B: Tauberian 定理 (Wiener-Ikehara / Newman)
  └── 向 Mathlib 贡献围道积分、留数定理

远期
  ├── 阶段 V: 素数定理 (PNT)
  ├── 阶段 VI: ζ 函数零点理论
  └── 阶段 VI: 黎曼猜想 (陈述与已知结果)
```

---

### 对 Mathlib 社区的建议

阶段 4 以后的工作高度依赖 Mathlib 中尚不存在的基础设施。建议以向 Mathlib 贡献 PR 的方式推进, 特别是复分析工具和 ζ 函数理论。
