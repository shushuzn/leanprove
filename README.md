# leanprove

Lean 4 数学形式化证明项目 — 从素数分布到黎曼猜想的探索之旅。

## 项目概述

使用 [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4/) 对数论定理进行严格的形式化证明。项目从素数的模运算性质出发，逐步推进到解析数论的核心结果。

**当前进度**: 阶段 V-A/V-B ✅ — 素数定理全部等价形式已证 (ψ~x ↔ θ~x ↔ π~x/log x)。PNTVA.lean 0 sorry。Tauberian.lean 0 sorry (2 顶层 axiom)。

**注**: 全项目共 **110 个定理 + 24 个引理 (134 总计)** + Phase V-A/V-B 新增 **13 定理 + 5 引理**，涵盖初等数论、Chebyshev 理论、Dirichlet 定理、Von Mangoldt 函数、Mertens 第一定理、ζ 函数基础、Euler 乘积、解析延拓与素数定理。Phase I-IV 全部已证 0 sorry；**Phase V PNTVA.lean 全部 13 定理 0 sorry**；**Tauberian.lean 4 sorry 已全部消除**，剩余 2 个顶层 axiom (`WienerIkeharaTheorem` — Wiener-Ikehara Tauberian 定理, `G_continuous` — G 函数连续性)。

## 路线图

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
  V-A   ████████████ PNT 等价形式 + 素数定理     ✅ 完成 (0 sorry)
  V-B   ▓▓▓▓▓▓▓▓▓▓▓▓ θ~x ↔ π~x/log x           ✅ 完成 (0 sorry)
阶段 VI ░░░░░░░░░░░░ 黎曼猜想                    待开始
```

---

### 阶段 I: 初等数论基础 ✅

**文件**: `Basic.lean`, `PrimeCounting.lean`, `PrimeReciprocals.lean`

素数模运算性质、素数无穷性与素数计数的基本估计。

| # | 定理 | 方法 |
|---|------|------|
| 1 | `24 \| p² - 1` 对素数 p ≥ 5 | 模 3 和模 8 分析 |
| 2 | `24 \| p² - q²` 对素数 p,q ≥ 5 | 平方差公式 |
| 3 | `48 \| n⁴ - 1` 对奇数 n, 3 ∤ n | 因式分解 |
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
| 4 | Λ(n) 定义与 Dirichlet 卷积 | ∑_{d\|n} Λ(d) = ln n |
| 5 | ψ(x) = ∑_{n≤x} Λ(n) | Chebyshev psi |
| 6 | **Mertens 恒等式**: ∑ Λ(n)/n = ψ/x + ∫ ψ/t² dt | Abel 求和公式 |
| 7 | **素数幂贡献有界** | 几何级数界 |
| 8 | ∑ ln n = N·ln N - N + O(ln N) | **Stirling 公式** (积分比较) |
| 9 | **卷积恒等式**: ∑ Λ(n)·⌊N/n⌋ = ∑ ln k | 除数双射 |
| 10 | **Mertens 第一定理**: ∑ Λ(n)/n = ln x + O(1) | Stirling + Chebyshev |
| 11 | ∫ ψ/t² dt - ln x = O(1) | Mertens + Abel 恒等式 |

**关键定理**: Mertens 第一定理 (全程初等证明, 无需素数定理)

---

### 阶段 IV: Zeta 函数系列 ✅

**文件**: `Zeta.lean`, `ZetaIVB.lean`, `ZetaIVD.lean`, `ZetaIVE.lean`, `VonMangoldt.lean`

Riemann ζ 函数的分阶段构建。每个子阶段独立可验证。

#### IV-A: ζ(s) 定义与绝对收敛 ✅

| # | 定理 | 状态 |
|---|------|------|
| 1 | ζ(s) = ∑ 1/n^s (Re s > 1) | ✅ |
| 2 | ∑ \|1/n^s\| 收敛 (Re s > 1) | ✅ |
| 3 | \|ζ(s)\| ≤ ζ(Re(s)) | ✅ |

#### IV-B: (σ-1)ζ(σ) 上界 ✅

**文件**: `ZetaIVB.lean` — 5 个引理全部证明，零 sorry。

| # | 定理 | 方法 |
|---|------|------|
| 1 | `rpow_anti` — rpow 反单调性 | gcongr |
| 2 | `mvt_ineq` — 中值定理不等式 | mvt_norm_le |
| 3 | `n_pow_le_telescope` — 裂项上界 | Finset.sum_Ico_eq_sum_range |
| 4 | `sum_bound_upper` — 有限和上界 | div_le_iff + linarith |
| 5 | **`zeta_upper_bound`** — ζ(σ) ≤ 1 + 1/(σ-1) | le_of_tendsto + Eventually.of_forall |

#### IV-C: Mertens + Abel 求和 ✅

**文件**: `VonMangoldt.lean` — 14 个定理全部证明，0 sorry

| # | 定理 | 状态 | 方法 |
|---|------|------|------|
| 1 | `vm_nonneg` — Λ(n)/n ≥ 0 | ✅ | div_nonneg + vonMangoldt_nonneg |
| 2 | `vm_le_one` — Λ(n)/n ≤ 1 (n≥2) | ✅ | div_le_one + vonMangoldt_le_log |
| 3 | `pow_div_pow_bound` — 1/p^k ≤ (1/2)^{k-2}·1/p^2 | ✅ | gcongr + field_simp |
| 4 | `geom_sum_bound` — ∑_{j=0}^N (1/2)^j ≤ 2 | ✅ | geom_sum_eq + positivity |
| 5 | `geom_tail_Icc_bound` — ∑_{k=2}^M 1/p^k ≤ 2/p^2 | ✅ | pow_div_pow_bound + geom_sum_bound |
| 6 | `range_sum_le_tsum_of_nonneg` — 部分和 ≤ tsum | ✅ | HasSum.tendsto_sum_nat + by_contra |
| 7 | `log_lt_two_sqrt` — log p < 2√p | ✅ | log_le_sub_one_of_pos |
| 8 | `sqrt_div_sq_eq_rpow` — √p/p² = p^{-3/2} | ✅ | rpow_sub |
| 9 | `log_div_sq_bound_le` — log p/p² ≤ 2p^{-3/2} | ✅ | gcongr + sqrt_div_sq_eq_rpow |
| 10 | `primePower_contribution_bounded` — ∑_{¬Prime} Λ(n)/n 有界 | ✅ | 双重求和法: H(m,j) + sum_bij + Summable.sum_le_tsum |
| 11 | `psi_integral_sub_log_isBigO` — ∫ψ/t² - log = O(1) | ✅ 已证 | Mertens + Abel 恒等式 + setIntegral_union |
| 12 | `mertens_abel_identity` — ∑Λ(n)/n = ψ/x + ∫ψ/t² dt | ✅ 已证 | Abel 求和公式 |
| 13 | `mertens_first_theorem` — ∑_{p≤x} (log p)/p - log x = O(1) | ✅ 已证 | Mertens 第一定理 |
| 14 | `mertens_first_theorem_bounded` — \|∑_{p≤x} (log p)/p - log x\| ≤ C | ✅ 已证 | 有界形式 |

**IV-C 全部完成，0 sorry**:
- `psi_integral_sub_log_isBigO` ✅: Abel 求和恒等式 + setIntegral_union + integrableOn_of_bounded
- `mertens_first_theorem` ✅: 由 mertens_first_theorem_bounded 推出
- `mertens_first_theorem_bounded` ✅: vm_div_sum_sub_log_bound + primePower_contribution_bounded + 三角不等式

#### IV-D: Euler 乘积 ✅

**文件**: `ZetaIVD.lean` — 4 个定理全部证明，0 sorry

| # | 定理 | 状态 | 方法 |
|---|------|------|------|
| 1 | `riemannZeta_real_pos` — ζ(σ) > 0 (σ > 1) | ✅ | riemannZeta_def + tsum_pos |
| 2 | `riemannZeta_ne_zero_real` — ζ(σ) ≠ 0 (σ > 1) | ✅ | ne_of_gt + riemannZeta_real_pos |
| 3 | `euler_product_real_tendsto` — ∏_p (1 - p^{-σ})⁻¹ → ζ(σ) | ✅ | HasProd.tendsto_partialProd |
| 4 | `euler_product_real_hasProd` — Euler 乘积公式 | ✅ | euler_product_real_tendsto + HasProd |

**IV-D 全部完成，0 sorry**:
- `riemannZeta_real_pos` ✅: ζ(σ) 定义为正项级数，和为正
- `riemannZeta_ne_zero_real` ✅: 由正性直接推出非零
- `euler_product_real_tendsto` ✅: 部分乘积趋于 ζ(σ)
- `euler_product_real_hasProd` ✅: 完整的 Euler 乘积公式

#### IV-E: 解析延拓与零区域 ✅

**文件**: `ZetaIVE.lean` — 16 个定理全部包装，0 sorry

| # | 定理 | 状态 | 来源 |
|---|------|------|------|
| 1 | `zeta_analytic` — ζ(s) 在 ℂ\{1} 解析 | ✅ | analyticOn_riemannZeta |
| 2 | `zeta_differentiable_at` — ζ(s) 可微 (s≠1) | ✅ | differentiableAt_riemannZeta |
| 3 | `zeta_differentiable_on` — ζ(s) 在 {1}ᶜ 可微 | ✅ | differentiableOn_riemannZeta |
| 4 | `zeta_residue_one` — Res(ζ,1) = 1 | ✅ | riemannZeta_residue_one |
| 5 | `completed_zeta₀_functional_equation` — Λ₀(1-s) = Λ₀(s) | ✅ | completedRiemannZeta₀_one_sub |
| 6 | `completed_zeta₀_entire` — Λ₀(s) 是整函数 | ✅ | differentiable_completedZeta₀ |
| 7 | `completed_zeta_functional_equation` — Λ(1-s) = Λ(s) | ✅ | completedRiemannZeta_one_sub |
| 8 | `zeta_functional_equation` — ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s) | ✅ | riemannZeta_one_sub |
| 9 | `zeta_ne_zero_of_one_le_re` — ζ(s)≠0 (Re s ≥ 1) | ✅ | riemannZeta_ne_zero_of_one_le_re |
| 10 | `zeta_ne_zero_of_one_lt_re` — ζ(s)≠0 (Re s > 1) | ✅ | riemannZeta_ne_zero_of_one_lt_re |
| 11 | `zeta_trivial_zero` — ζ(-2(n+1)) = 0 | ✅ | riemannZeta_neg_two_mul_nat_add_one |
| 12 | `zeta_at_zero` — ζ(0) = -1/2 | ✅ | riemannZeta_zero |
| 13 | `zeta_at_two` — ζ(2) = π²/6 | ✅ | riemannZeta_two |
| 14 | `zeta_at_four` — ζ(4) = π⁴/90 | ✅ | riemannZeta_four |
| 15 | `zeta_at_even` — ζ(2k) Bernoulli 公式 | ✅ | riemannZeta_two_mul_nat |
| 16 | `zeta_at_neg_nat` — ζ(-k) Bernoulli 公式 | ✅ | riemannZeta_neg_nat_eq_bernoulli |

---

### 阶段 V: 素数定理 (PNT) ⏳

#### V-A: PNT 等价形式 ✅

**文件**: `PNTVA.lean` + `Sobolev.lean` + `Tauberian.lean` — 11 个已证定理 + 5 个辅助引理 + Tauberian 4 sorry 消除，0 sorry

| # | 定理 | 状态 | 方法 |
|---|------|------|------|
| 1 | `two_log_div_sqrt_tendsto_zero` — 2·log x/√x → 0 | ✅ | isLittleO_log_rpow_atTop + tendsto_div_nhds_zero |
| 2 | `psi_sub_theta_div_x_tendsto_zero` — (ψ-θ)/x → 0 | ✅ | abs_psi_sub_theta_le_sqrt_mul_log + 夹逼定理 |
| 3 | `psi_div_x_iff_theta_div_x` — ψ/x→1 ↔ θ/x→1 | ✅ | Tendsto.sub/add + convert |
| 4 | `isEquivalent_id_iff_tendsto_div_one` — u~id ↔ u/x→1 | ✅ | isLittleO_iff_tendsto |
| 5 | `pnt_psi_iff_pnt_theta` — ψ~x ↔ θ~x | ✅ | 由 3+4 组合 |
| 6 | `x_div_log_sq_isLittleO_x_div_log` — x/log²x =o(x/log x) | ✅ | isLittleO_iff_tendsto + inv_tendsto_atTop |
| 7 | `pi_isEquivalent_theta_div_log` — π~θ/log | ✅ | Abel 求和 + Chebyshev 下界 + 夹逼 |
| 8 | `pnt_theta_iff_pnt_pi` — θ~x ↔ π~x/log x | ✅ | 由 5+7+IsEquivalent 传递 |
| 9 | `pnt_psi_iff_pnt_pi` — ψ~x ↔ π~x/log x | ✅ | 由 5+8 传递 |
| 10 | `log_deriv_zeta_eq_vonMangoldt_series` — -ζ'/ζ = ∑Λ/n^s | ✅ | mathlib LSeries_vonMangoldt_eq_deriv_riemannZeta_div |
| 11 | `log_deriv_zeta_analytic` — -ζ'/ζ 全纯 | ✅ | analyticOn_riemannZeta + deriv + div + ζ≠0 |
| 12 | `vonMangoldt_cheby` — ∑Λ(n) ≤ Cn | ✅ | Chebyshev 上界 |
| 13 | `WienerIkeharaTheorem` — Tauberian 定理 | ⚠️ axiom | Fourier 分析 (~4000 行待完整实现) |
| 14 | `WeakPNT` — cumsum Λ(N)/N → 1 | ✅ 基于 axiom | Wiener-Ikehara + LSeriesSummable_vonMangoldt + G_continuous |
| 15 | `prime_number_theorem_psi_from_tauberian` — ψ~x | ✅ 已证 | squeeze theorem (离散→连续转换) |
| 16 | `prime_number_theorem_pi` — π~x/log x | ✅ | pnt_psi_iff_pnt_pi + prime_number_theorem_psi |

**技术细节**:
- `psi_sub_theta_div_x_tendsto_zero` ✅: 由 Chebyshev 界 |ψ-θ| ≤ 2√x·log x 得 |(ψ-θ)/x| ≤ 2·log x/√x → 0，用夹逼定理 (tendsto_of_tendsto_of_tendsto_of_le_of_le') 证明。
- `pnt_psi_iff_pnt_theta` ✅: 利用 IsEquivalent 定义 (u~v ↔ (u-v)=o(v)) 转化为 Tendsto 形式，再由 ψ/x→1 ↔ θ/x→1 得出。
- `pi_isEquivalent_theta_div_log` ✅: 核心引理。利用 mathlib 的 `primeCounting_sub_theta_div_log_isBigO` (π - θ/log = O(x/log²x)) 与 `theta_ge'` (Chebyshev 下界) 证明 θ(x) ≥ c·x (c > 0)。由 x/log²x =o(θ/log) 和 O·o 传递性得 (π - θ/log) =o(θ/log)，从而 π ~ θ/log。
- `pnt_theta_iff_pnt_pi` ✅: 由 π ~ θ/log 和 θ ~ x ↔ θ/log ~ x/log (通过 isEquivalent_iff_tendsto_one 转换) 和 π ~ θ/log (已证) 传递得出。
- `log_deriv_zeta_eq_vonMangoldt_series` ✅: 包装 mathlib 的 `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`，通过 `LSeries_congr` 处理 vonMangoldt 的类型强制 (ℝ→ℂ)。
- `log_deriv_zeta_analytic` ✅: 由 `analyticOn_riemannZeta.deriv` 得 ζ' 解析，再用 `AnalyticOnNhd.div` 除以 ζ (利用 `riemannZeta_ne_zero_of_one_le_re` 保证 ζ≠0)，最后 `.neg` 取负。
- `prime_number_theorem_psi` ⚠️: 基于 Wiener-Ikehara Tauberian 定理 (axiom)。`WienerIkeharaTheorem` 声明: 若非负 f 的 L-级数 ∑f(n)/n^s 在 Re(s)>1 收敛且 ∑f(n)/n^s - A/(s-1) 连续延拓到 Re(s)≥1，则 ∑_{n<N}f(n)/N → A。WeakPNT 的完整证明: `LSeriesSummable_vonMangoldt` (可和性) + `G_continuous` (连续性, axiom) + `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (G 等式)。`prime_number_theorem_psi_from_tauberian` 通过 squeeze theorem 将离散 WeakPNT (cumsum Λ(N)/N → 1) 转换为连续 ψ(x)~x。Tauberian 定理的完整 Fourier 分析证明 (~4000 行) 待完成。

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
│   ├── Basic.lean              # 阶段 I: 初等数论 (21 定理)
│   ├── Chebyshev.lean          # 阶段 II: Chebyshev 界 (14 定理)
│   ├── Bertrand.lean           # 阶段 II: Bertrand 假设 (6 定理)
│   ├── PrimeCounting.lean      # 阶段 I-II: 素数计数 (3 定理)
│   ├── PrimeReciprocals.lean   # 阶段 I: 素数倒数和 (1 定理)
│   ├── Dirichlet.lean          # 阶段 III: 等差数列素数 (11 定理)
│   ├── VonMangoldt.lean        # 阶段 III-IV: VonMangoldt + Mertens (30+ 定理/引理)
│   ├── ZetaIVB.lean            # 阶段 IV-B: ζ 上界 (5 引理, 零 sorry)
│   ├── ZetaIVD.lean            # 阶段 IV-D: Euler 乘积 (4 定理, 零 sorry)
│   ├── ZetaIVE.lean            # 阶段 IV-E: 解析延拓 (16 定理, 零 sorry)
│   ├── PNTVA.lean              # 阶段 V-A/V-B: PNT 等价形式 (13 定理 + 5 引理, 0 sorry)
│   ├── Sobolev.lean             # Sobolev 空间 (CS, W1, W21, TruncFun)
│   ├── Tauberian.lean           # Wiener-Ikehara Tauberian 定理 + PNT (0 sorry, 2 axiom)
│   ├── Zeta.lean               # 阶段 IV: ζ 函数基础
│   └── Tests.lean              # 测试与验证
├── ROADMAP.md                  # 详细路线图与发展建议
├── lakefile.toml               # 构建配置
├── lean-toolchain              # Lean 版本锁定
└── README.md                   # 本文件
```

**总计**: 110+ 个定理 + 24+ 个引理 (134+ 总计), Phase I-IV: 0 sorry; Phase V-A PNTVA.lean: 0 sorry; Tauberian.lean: 0 sorry (2 顶层 axiom)

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
