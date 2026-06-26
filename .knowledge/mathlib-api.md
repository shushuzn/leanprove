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

## 12. 关键 Pitfalls（跨文件）

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
