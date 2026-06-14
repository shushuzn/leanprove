# Fourier 变换 API

## fourier_deriv

**Import**: `Mathlib.Analysis.Fourier.FourierTransformDeriv`
**签名**:
```lean
fourier_deriv {f : ℝ → E} (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x)
```
**说明**: 导数公式 `𝓕(deriv f) = (2πIu) • 𝓕(f)`。

## fourierIntegral_continuous

**Import**: `Mathlib.Analysis.Fourier.FourierTransform`
**签名**:
```lean
fourierIntegral_continuous (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {f : V → E} (hf : Integrable f μ) : Continuous (fourierIntegral e μ L f)
```
**说明**: L¹ 函数的 Fourier 变换连续。

## norm_fourierIntegral_le_integral_norm

**Import**: `Mathlib.Analysis.Fourier.FourierTransform`
**签名**:
```lean
norm_fourierIntegral_le_integral_norm : ‖𝓕 f u‖ ≤ ∫ t, ‖f t‖
```
**说明**: ‖𝓕(f)‖ ≤ ∫‖f‖。Fourier 变换的有界性。

## 二阶导数处理

```lean
-- deriv^[2] f = deriv (deriv f)
rw [← iteratedDeriv_eq_iterate (n := 2), iteratedDeriv_succ, iteratedDeriv_one]
```
