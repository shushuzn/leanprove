# 积分相关 API

## integral_mono

**Import**: `Mathlib.MeasureTheory.Integral.Integral`
**签名**:
```lean
integral_mono (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ᵐ a ∂μ, f a ≤ g a) : ∫ f ∂μ ≤ ∫ g ∂μ
```
**说明**: 比较积分。f 和 g 都必须可积。

## integral_add

**Import**: `Mathlib.MeasureTheory.Integral.Integral`
**签名**:
```lean
integral_add (hf : Integrable f μ) (hg : Integrable g μ) : ∫ (f + g) ∂μ = ∫ f ∂μ + ∫ g ∂μ
```

## integral_mul_const

**Import**: `Mathlib.MeasureTheory.Integral.Integral`
**签名**:
```lean
integral_mul_const (c : ℝ) (f : α → ℝ) : ∫ f * c ∂μ = (∫ f ∂μ) * c
```
**Pitfall**: 这是 `∫ f * c`，不是 `∫ c * f`。对于后者，先 `rw [mul_comm]` 或直接用 `integral_const_mul`。

## integral_const_mul

**Import**: `Mathlib.MeasureTheory.Integral.Integral`
**签名**:
```lean
integral_const_mul (c : ℝ) (f : α → ℝ) : ∫ (c * f) ∂μ = c * ∫ f ∂μ
```

## Integrable 系列

**Import**: `Mathlib.MeasureTheory.Integral.Integrable`

| 引理 | 作用 |
|------|------|
| `Integrable.norm hf` | 范数可积 |
| `Integrable.smul (c : 𝕜) hf` | 标量乘法可积（⚠️ 需显式提供标量类型） |
| `Integrable.const_mul c hf` | 常数乘法可积 |
| `Integrable.add hf hg` | 加法可积 |
| `Integrable.sub hf hg` | 减法可积 |

## Integrable.mono

**Import**: `Mathlib.MeasureTheory.Integral.Integrable`
**签名**:
```lean
Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ
```
**说明**: 用大函数 g 的可积性证明小函数 f 的可积性。
**Pitfall**: 参数顺序是 hg → hf → h（大函数先出现）。
```lean
-- 标准用法:
have h_bound : ∀ᵐ u, ‖f u‖ ≤ ‖g u‖ := Filter.Eventually.of_forall (by
  intro u; calc ‖f u‖ ≤ ... := ... _ ≤ ‖g u‖ := ...)
exact hg_int.mono h_meas h_bound
```

## AEStronglyMeasurable

**Import**: `Mathlib.MeasureTheory.Function.AEMeasurable`

| 方法 | 说明 |
|------|------|
| `Continuous.aestronglyMeasurable hf` | 连续函数可测 |
| `AEStronglyMeasurable.smul hc hf` | 标量乘法的可测组合 |

```lean
-- standard pattern:
have h_meas : AEStronglyMeasurable f volume := by
  apply (continuous_f).aestronglyMeasurable.comp_measurable
  exact measurable_g  -- e.g., measurable_id.div_const c
```

## integrable_comp_mul_left_iff

**Import**: `Mathlib.MeasureTheory.Integral.Integral`
**签名**:
```lean
integrable_comp_mul_left_iff (f : ℝ → F) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R * x)) ↔ Integrable f
```
**说明**: 变量替换。`f(a*x)` 可积 ↔ `f(x)` 可积。
```lean
rw [integrable_comp_mul_left_iff f (inv_ne_zero hc)]
exact integrable_f
```

## 指数衰减可积性（second_fourier_integrable_aux1a 适用）

**Import**: `Mathlib.MeasureTheory.Integral.ExpDecay`, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`

| 引理 | 签名 | 说明 |
|------|------|------|
| `exp_neg_integrableOn_Ioi` | `(a : ℝ) → 0 < b → IntegrableOn (fun x : ℝ => exp (-b * x)) (Ioi a)` | 核心：任意衰减率 b > 0 |
| `integrable_of_isBigO_exp_neg` | `0 < b → ContinuousOn f (Ici a) → f =O[atTop] (fun x => exp (-b * x)) → IntegrableOn f (Ioi a)` | BigO 界 + 连续 → 可积 |
| `integrableOn_exp_neg_Ioi` | `IntegrableOn (fun x => exp (-x)) (Ioi c)` | 衰减率 1 特例 |
| `MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi` | `IntegrableOn f (Ici a) ↔ IntegrableOn f (Ioi a)` | `Ici`↔`Ioi` 桥接（单点零测） |

**模式**（`cexp (-(x·(σ'-1)))` 在 `Ici (-log x)` 上可积，σ' > 1）：
```lean
rw [integrableOn_Ici_iff_integrableOn_Ioi]
-- 复指数模长 = 实指数：‖cexp z‖ = exp z.re
apply Integrable.mono (exp_neg_integrableOn_Ioi _ (by linarith : (0:ℝ) < σ' - 1)) h_meas
-- ‖cexp (-(x·(σ'-1)))‖ = exp (-(σ'-1)·x)，用 Complex.norm_exp / Complex.exp_ofReal_re
```

## 乘积测度可积性（second_fourier_integrable_aux1 适用）

**Import**: `Mathlib.MeasureTheory.Integral.Prod`

| 引理 | 签名 | 说明 |
|------|------|------|
| `MeasureTheory.integrable_prod_iff` | `AEStronglyMeasurable f (μ.prod ν) → (Integrable f (μ.prod ν) ↔ (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ)` | Tonelli 判别：截面可积 + 范数积分可积 |
| `MeasureTheory.integrable_prod_iff'` | 对称版本（先对 x 后对 y），需 `[SFinite μ]` | |

**Pitfall**: `Function.uncurry f` 形式的目标先 `rw [Function.uncurry]` 或用 `(x, y)` 模式匹配；可测性前提用 `Continuous.aestronglyMeasurable` + 乘积连续性组合。

## ENNReal tsum 与 Summable 桥接（hf_coe1 适用）

**Import**: `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`（定理在 `ENNReal` 命名空间）

| 引理 | 签名 | 说明 |
|------|------|------|
| `ENNReal.tsum_coe_ne_top_iff_summable` | `(∑' b, (f b : ℝ≥0∞)) ≠ ⊤ ↔ Summable f`（f : β → ℝ≥0） | 核心桥接 |
| `ENNReal.tsum_coe_ne_top_iff_summable_coe` | `(∑' b, (f b : ℝ≥0∞)) ≠ ⊤ ↔ Summable (fun b => (f b : ℝ))` | 直接到 ℝ 版本 |

**模式**（`hf_coe1`：从 `Summable (nterm f σ')` 推 `∑' i, (‖term f σ' i‖₊ : ℝ≥0∞) ≠ ⊤`）：
```lean
rw [ENNReal.tsum_coe_ne_top_iff_summable]
-- 目标: Summable fun i => ‖term f σ' i‖₊，从 nterm 的可和性 + NNReal.summable_coe 转换
exact (NNReal.summable_coe.mp ...) 或 Summable.toNNReal ...
```
**Pitfall**: `‖·‖₊`（nnnorm）与 `nterm` 的关系需要 `nterm_eq_norm_term` 先行改写。

