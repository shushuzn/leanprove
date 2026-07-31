# Mathlib API 索引

本文件汇总 `Leanprove` 项目中最常用的 Mathlib API。详细专题参见：
- BigO/渐近分析 → `bigo-api.md`
- nnabla / nabla 序列差分 → `nnabla-api.md`
- Fourier 变换 → `fourier-api.md`
- 积分与可积性 → `integral-api.md`
- 对数函数 → `log-api.md`
- 除法与域不等式 → `division-api.md`
- 范数 / Cast → `norm-cast-api.md`
- 连续可微 → `contdiff-api.md`

---

## 1. 渐近分析 (Asymptotics)

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`

| 引理 | 签名/用法 | 说明 |
|------|-----------|------|
| `IsBigO.of_bound` | `IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g` | 最常用 BigO 证明入口 |
| `IsBigO.of_bound'` | `IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g` | 常数 1 版本 |
| `IsBigO.add` | `IsBigO.add h₁ h₂ : (f₁ + f₂) =O[l] g` | 拆解和式 |
| `IsBigO.mul` | `IsBigO.mul h₁ h₂ : (f₁ * f₂) =O[l] (g₁ * g₂)` | 乘法组合 |
| `IsBigO.trans` | `IsBigO.trans hfg hgk : f =O[l] k` | 传递性 |
| `IsBigO.trans_le` | `IsBigO.trans_le hfg (fun x => ‖g' x‖ ≤ ‖k x‖) : f =O[l] k` | 传递 + 点态 bound |
| `IsBigO.comp_tendsto` | `IsBigO.comp_tendsto hfg hk : (f ∘ k) =O[l'] (g ∘ k)` | 变量替换 |
| `IsBigO.pow` / `.sq` | `IsBigO.pow h n : (fun x => f x ^ n) =O[l] fun x => g x ^ n` | 幂次 |
| `isBigO_of_le` | `isBigO_of_le (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g` | 全称 bound |
| `isBigO_const_of_tendsto` | 有界函数 =O(常数) | 常数 bound |
| `IsLittleO.isBigO` | `IsLittleO.isBigO h : f =O[l] g` | o ⊆ O |
| `isLittleO_const_of_tendsto_atTop` | 项目自定义：`(fun _ => a) =o[atTop] f`（当 `f → ∞`） | 常数 = o(f) |

**标准模式**: `apply IsBigO.of_bound C` → `filter_upwards [eventually_gt_atTop N]` → 点态不等式。

---

## 2. 序列差分 (nabla / nnabla)

**Import**: `Leanprove.WienerProof`（项目自定义）

| 引理 | 签名 | 说明 |
|------|------|------|
| `nabla` | `nabla u n = u (n + 1) - u n` | 正向差分 |
| `nnabla` | `nnabla u n = u n - u (n + 1)` | 负向差分 |
| `neg_nabla` | `-(nabla u) = nnabla u` | 关系 |
| `nabla_mul` / `nnabla_mul` | 常数乘法与差分交换 | `c • nabla u` |
| `summation_by_parts` | Abel 分部求和 | 项目自定义 |
| `cumsum_summation` | 通过差分证明级数可和 | 项目自定义 |

---

## 3. Fourier 变换

**Import**: `Mathlib.Analysis.Fourier.FourierTransformDeriv`, `Mathlib.Analysis.Fourier.FourierTransform`

| 引理 | 签名 | 说明 |
|------|------|------|
| `fourier_deriv` | `𝓕(deriv f) = fun x => (2πIx) • 𝓕 f x` | 导数公式 |
| `fourierIntegral_continuous` | 连续 Fourier 变换 | `L¹` 函数 |
| `norm_fourierIntegral_le_integral_norm` | `‖𝓕 f u‖ ≤ ∫ t, ‖f t‖` | 有界性 |

---

## 4. 积分与可积性

**Import**: `Mathlib.MeasureTheory.Integral.Integral`, `Mathlib.MeasureTheory.Integral.Integrable`

| 引理 | 签名 | 说明 |
|------|------|------|
| `integral_mono` | 可积函数比较积分 | f, g 都可积 |
| `integral_add` | `∫(f + g) = ∫f + ∫g` | 加法 |
| `integral_mul_const` | `∫(f * c) = (∫f) * c` | 右侧常数 |
| `integral_const_mul` | `∫(c * f) = c * ∫f` | 左侧常数 |
| `Integrable.norm` | 范数可积 | |
| `Integrable.smul` | 标量乘法可积 | ⚠️ 显式提供标量类型 |
| `Integrable.const_mul` | 常数乘法可积 | |
| `Integrable.add` / `.sub` | 加减法可积 | |
| `Integrable.mono` | 大函数可积 + 可测 + 点态 bound → 小函数可积 | |
| `integrable_comp_mul_left_iff` | `f(R*x)` 可积 ↔ `f(x)` 可积（R ≠ 0） | 变量替换 |
| `Continuous.aestronglyMeasurable` | 连续函数可测 | |

---

## 5. 对数函数

**Import**: `Mathlib.Analysis.SpecialFunctions.Pow.Real`

| 引理 | 签名 | 说明 |
|------|------|------|
| `Real.log_div` | `log(x/y) = log x - log y` | x, y ≠ 0 |
| `Real.log_mul` | `log(x*y) = log x + log y` | x, y ≠ 0 |
| `Real.log_pos` | `1 < x → 0 < log x` | |
| `Real.log_le_sub_one_of_pos` | `0 < x → log x ≤ x - 1` | 核心 bound |
| `Real.log_le_log` / `Real.log_lt_log` | 单调性 | 0 < x |
| `Real.log_le_log_iff` / `Real.log_lt_log_iff` | 带 iff 的单调性 | |

**常用**: `Real.exp_one_lt_three`（import `Mathlib.Analysis.Complex.ExponentialBounds`）用于 `eventually_gt_atTop 3`。

---

## 6. 除法与域不等式

**Import**: `Mathlib.Algebra.Order.Field.Basic`

| 引理 | 签名 | 说明 |
|------|------|------|
| `div_sub_one` | `a/b - 1 = (a - b)/b` | b ≠ 0 |
| `one_lt_div` | `0 < b → (1 < a/b ↔ b < a)` | |
| `div_lt_iff₀` | `0 < c → a/c < b ↔ a < b*c` | |
| `lt_div_iff₀'` | `0 < c → a < b/c ↔ a*c < b` | |
| `div_le_div_of_nonneg_right` | `a ≤ b → 0 ≤ c → a/c ≤ b/c` | |

---

## 7. 范数与绝对值

**Import**: `Mathlib.Analysis.NormedSpace.Basic`

| 引理 | 签名 | 说明 |
|------|------|------|
| `Real.norm_eq_abs` | `‖x‖ = |x|`（x : ℝ） | 实数范数转绝对值 |
| `norm_real` | `‖(↑x : ℂ)‖ = ‖x‖` | 复数→实数范数 |
| `norm_mul` | `‖a*b‖ = ‖a‖*‖b‖` | |
| `norm_add_le` | `‖a+b‖ ≤ ‖a‖ + ‖b‖` | 三角不等式 |
| `norm_sub_le` | `‖a-b‖ ≤ ‖a‖ + ‖b‖` | |
| `abs_sub` | `|a-b| ≤ |a| + |b|` | |
| `abs_add_three` | `|a+b+c| ≤ |a|+|b|+|c|` | 三项三角不等式 |
| `abs_of_pos` / `abs_of_nonneg` | 去掉绝对值 | |

---

## 8. 连续可微 (ContDiff)

**Import**: `Mathlib.Analysis.Calculus.ContDiff`

| 引理/方法 | 说明 |
|-----------|------|
| `ContDiff.continuous_deriv` | C^n 导数连续 |
| `ContDiff.deriv'` | C^(n+1) → C^n 导数 |
| `ContDiff.continuous_deriv_one` | C^1 导数连续 |
| `HasCompactSupport.deriv` | 紧支集导数仍紧支集 |
| `continuous_of_compactSupport.integrable_of_hasCompactSupport` | 紧支集连续函数可积 |

---

## 9. 常用代数/不等式

| 引理 | 说明 |
|------|------|
| `sub_le_self` | `0 ≤ b → a - b ≤ a` |
| `mul_inv_cancel_left₀` | `(x-1)*(1/(x-1)) = 1` |
| `sq_nonneg` | `a² ≥ 0` |
| `abs_nonneg` | `|a| ≥ 0` |

---

## 10. 项目自定义关键引理

位于 `Leanprove.WienerProof` 或相关项目文件：

| 引理 | 签名 | 说明 |
|------|------|------|
| `isLittleO_const_of_tendsto_atTop` | `(fun _ => a) =o[atTop] f`（f → ∞） | |
| `log_add_div_isBigO_log` | `log((x+a)/b) =O[atTop] log x` | |
| `nabla_log` | `log((x+1)/b) - log(x/b) =O[atTop] 1/x` | |
| `log_isbigo_log_div` | `log n =O[atTop] log(n/d)` | |
| `log_sq_isbigo_mul` | `(log x)² =O[atTop] a + (log(x/b))²` | |
| `Asymptotics.IsBigO.add_isLittleO_right` | `g =o f → f =O (f + g)` | |

---

## 11. 通用证明策略速查

| 目标 | 策略 |
|------|------|
| 等式（含除法） | `field_simp`（注意 pitfall：在 `show ... from by` 内部会关闭目标） |
| 环等式 | `ring_nf` / `ring` |
| Cast | `push_cast` / `norm_cast` |
| 正数/非负 | `positivity` / `linarith` |
| 最终足够大 | `filter_upwards [eventually_gt_atTop N]` |
| 绝对值 | `abs_of_pos`, `abs_of_nonneg`, `abs_mul` |

---

## 12. 可和性判别 (Summability)

**Import**: `Mathlib.Analysis.PSeries`（已在 .lake 源码中逐条确认）

| 引理 | 签名 | 说明 |
|------|------|------|
| `summable_condensed_iff_of_nonneg` | `(∀ n, 0 ≤ f n) → (∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) → ((Summable fun k : ℕ => 2^k * f (2^k)) ↔ Summable f)` | Cauchy 凝聚判别，`summable_inv_mul_log_sq` 的关键 |
| `summable_condensed_iff` | 同上，`ℝ≥0` 版本 | |
| `summable_one_div_nat_rpow` | `Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p` | 实数幂 |
| `summable_one_div_nat_pow` | `Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 2 ≤ p`（p : ℕ） | 自然数幂 |
| `summable_one_div_int_pow` | 整数版本 | |

**⚠️ 重要**: Mathlib **没有** 现成的 `1/(n·(log n)²)` 可和引理（全库 grep `summable.*log` 无匹配）。
证明 `summable_inv_mul_log_sq` 的路线：用 `summable_condensed_iff_of_nonneg` 凝聚化，
`2^k · 1/(2^k·(k·log 2)²) = 1/(k²·(log 2)²)`，归结到 `summable_one_div_nat_pow`（p=2）× 常数。
注意需先处理 n=0,1 的项（log 为 0，项为 ⊤⁻¹=0 或用 `Summable.congr_atTop`）。

---

## 13. 控制收敛定理 (Dominated Convergence)

**Import**: `Mathlib.MeasureTheory.Integral.DominatedConvergence`

| 引理 | 签名要点 | 说明 |
|------|----------|------|
| `MeasureTheory.tendsto_integral_of_dominated_convergence` | `(bound : α → ℝ) → (∀ n, AEStronglyMeasurable (F n) μ) → (∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) → Integrable bound μ → (∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) → Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ))` | 序列版（ℕ 指标） |
| `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` | 同上，但指标是任意 `[l.IsCountablyGenerated]` 的 filter，且前两个条件是 `∀ᶠ n in l, ...` | **`𝓝[>] 1` 版本用这个**，适用 `limiting_fourier_lim1/lim2/lim3`（σ' → 1⁺） |

**模式**（lim3 类型目标：σ' → 1⁺ 时积分收敛）：
```lean
apply tendsto_integral_filter_of_dominated_convergence bound
· -- ∀ᶠ σ' in 𝓝[>] 1, AEStronglyMeasurable ...
  filter_upwards [self_mem_nhdsWithin] with σ' hσ' ...
· -- ‖G(σ'+tI)·ψ t·x^(tI)‖ ≤ bound t（用 ψ 紧支集 + G 局部一致界）
· -- Integrable bound（紧支集连续函数）
· -- 逐点收敛：G 连续性 + Tendsto.comp
```

---

## 14. 解析函数零点离散性 (Isolated Zeros)

**Import**: `Mathlib.Analysis.Analytic.IsolatedZeros`

| 引理 | 签名 | 说明 |
|------|------|------|
| `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` | `AnalyticAt 𝕜 f z₀ → (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0)` | 零点要么局部恒零要么孤立 |
| `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` | 连通开集上：恒零 ∨ 零点孤立 | 用于 `criticalLineZeros_isDiscrete`：ξ 不恒零（ξ(2)≠0）→ 零点孤立 → 离散 |
| `AnalyticOnNhd.preimage_mem_codiscreteWithin` | 零点集余离散 | codiscrete 表述 |

**DiscreteTopology 路线**: 孤立零点 → 每点有邻域仅含该零点 → `singletons_open_iff_discrete` / `discreteTopology_subtype_iff`。

---

## 15. 集合计数 (Nat.card / ENat.card / encard)

**Import**: `Mathlib.Data.Set.Card`

⚠️ **本项目实际用的是 `Nat.card` 与 `ENat.card`，不是 `Set.ncard`**（已核实 Definitions.lean）：
- `criticalLineZeroCount T : ℕ = Nat.card {t : ℝ | ...}`
- `xiZeroCount T : ℕ∞ = ENat.card {s : ℂ | ...}`

| 引理 | 签名 | 说明 |
|------|------|------|
| `ENat.card_coe_set_eq` | `ENat.card s = s.encard`（rfl，@[simp]） | ENat.card ↔ encard 桥接 |
| `Set.encard_le_encard` | `s ⊆ t → s.encard ≤ t.encard` | 子集单调（无需有限） |
| `Set.encard_mono` | `Monotone (encard : Set α → ℕ∞)` | 单调性版 |
| `Set.encard_le_encard_of_injOn` | `MapsTo f s t → InjOn f s → s.encard ≤ t.encard`（Card.lean:507） | **单射像计数，`criticalLineZeroCount_le_xiZeroCount` 首选** |
| `Nat.card_le_card_of_injective` | `Injective f → Nat.card α ≤ Nat.card β`（需 β 有限） | 子型 Nat.card |

**`criticalLineZeroCount_le_xiZeroCount` 路线**（注意两边类型不同：`↑(Nat.card ...) ≤ ENat.card ...`）：
注入映射是 `criticalLine : ℝ → ℂ`（`t ↦ 1/2 + I·t`，显然单射）。先把 `Nat.card` 转为 `encard`
（`Nat.card_eq_toNat_card` / `ENat.card_coe_set_eq` + 有限性），再用 `encard_le_encard_of_injOn`
将临界线零点集嵌入 ξ 零点集。
**Pitfall**: `Nat.card` 对无限集为 0；若右侧 `ENat.card` 为 ⊤（零点无限）不等式平凡成立。encard 路线自动处理无限情形，优于先假设有限。

---

## 16. Zeta/LSeries 可微性

**Import**: `Mathlib.NumberTheory.LSeries.RiemannZeta`

| 引理 | 签名 | 说明 |
|------|------|------|
| `differentiableAt_riemannZeta` | `s ≠ 1 → DifferentiableAt ℂ riemannZeta s` | ζ 在 s≠1 处可微（→ 连续） |
| `differentiable_completedZeta₀` | `Differentiable ℂ completedRiemannZeta₀` | 完备 zeta 全局可微 |
| `differentiableAt_completedZeta` | `s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ completedRiemannZeta s` | |

**⚠️ 缺失警告**: Mathlib 当前**没有** `norm_Gamma_le` / `abs_Gamma` 型垂直条带 Stirling 上界（全 Analysis 目录 grep 无匹配）。
Definitions.lean L249（`≤ C·(1+|t|)^{3/2}` 型 Gamma bound）需自证或换路线，详见 `difficult-proofs.md`。

---

## 17. 关键 Pitfalls（跨文件）

### ⚠️ riemannXi_conj 证明策略
**Import**: `Leanprove.CriticalLine.Definitions`, `Mathlib.Analysis.MellinTransform`
**核心性质**: `completedRiemannZeta (conj s) = conj (completedRiemannZeta s)`
**证明链**: `completedRiemannZeta s = mellin (ofReal ∘ evenKernel 0) (s/2) / 2` → `mellin f (conj s) = conj (mellin f s)`（实值函数，用 `integral_conj`）→ `completedRiemannZeta (conj s) = conj (completedRiemannZeta s)` → `riemannXi_conj`
**Pitfall**: `completedHurwitzZetaEven` 和 `evenKernel` 不在顶层命名空间，需要通过 `HurwitzZetaEven` 或直接展开定义访问。

### ⚠️ riemannZeta_def_of_ne_zero 模式
**Import**: `Mathlib.NumberTheory.LSeries.RiemannZeta`
**签名**: `s ≠ 0 → riemannZeta s = completedRiemannZeta s / Gammaℝ s`
**说明**: 用于从 `completedRiemannZeta s = 0` 推导 `riemannZeta s = 0`（结合 `zero_div`）
**Pitfall**: 需要 `s ≠ 0` 条件；`Gammaℝ s` 可能为 0（当 s 是负偶数时），但 `0 / 0 = 0` 在 Lean 中成立。

### ⚠️ mul_eq_zero + absurd 模式
```lean
-- 从 a * b = 0 且 a ≠ 0 推导 b = 0
rcases mul_eq_zero.mp h_zero with h | h
· exact absurd h h_prod_ne  -- a ≠ 0 矛盾
· exact h                   -- b = 0
```

### ⚠️ pi_lt_d2 用于数值 bound
**Import**: `Mathlib.Analysis.Real.Pi.Bounds`
**签名**: `pi_lt_d2 : π < 3.15`
**说明**: 用于证明 `π² < 12`（即 `π²/6 < 2`），结合 `nlinarith [pi_lt_d2, Real.pi_pos]`。

### ⚠️ riemannZeta_two 用于 ζ(2) 值
**Import**: `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`
**签名**: `riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6`

### ⚠️ riemannZeta_ne_zero_of_one_lt_re
**Import**: `Mathlib.NumberTheory.LSeries.Dirichlet`
**签名**: `1 < s.re → riemannZeta s ≠ 0`
**说明**: ζ(s) 在 Re s > 1 时非零（Euler 乘积推论）。

### ⚠️ Gamma_conj 用于 Γ 函数共轭
**Import**: `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`
**签名**: `Complex.Gamma_conj : Gamma (conj s) = conj (Gamma s)`
**说明**: 用于 Γ 函数的共轭性质。

### ⚠️ integral_conj 用于积分共轭
**Import**: `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`
**签名**: `integral_conj : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ)`
**说明**: 用于证明 Mellin 变换的共轭性质。

### ⚠️ Gammaℝ_ne_zero_of_re_pos
**Import**: `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`
**签名**: `0 < re s → Gammaℝ s ≠ 0`
**说明**: Γℝ(s) = π^{-s/2} Γ(s/2) 在 Re s > 0 时非零。

1. **`field_simp` 在 `show ... from by` 内部关闭目标**，后续 `ring_nf` 报 "No goals to be solved"。
2. **`rw [← Real.norm_eq_abs]` 在 `have` 内部影响主目标**，应使用 `rw [Real.norm_eq_abs] at this`。
3. **`linarith` 在 `filter_upwards` 内部可能看不到假设**，显式传递：`linarith [h1, h2]`。
4. **`Integrable.smul` 需显式提供标量类型**：`(W21.hf'' f).smul (↑c : ℂ)`。
5. **`integral_mul_const` 与 `integral_const_mul` 方向不同**。
6. **`simp` 可能将 `atTop` 变为 `Filter.atTop`**，导致 BigO filter 类型不匹配。
7. **双重绝对值**：`|(|a|)|` 需 `rw [abs_of_nonneg (abs_nonneg _)]` 简化。
8. **`div_pos (by linarith)` 在 `have` 内部可能失败**，显式提供类型：`div_pos (by linarith : 0 < x) hx1`。
