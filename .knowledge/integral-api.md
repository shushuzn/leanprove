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
