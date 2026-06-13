# Fourier 变换相关 API

## 核心定义

### Fourier 变换
```lean
-- ℝ 上的 Fourier 变换
𝓕 f u = ∫ v, 𝐞 (-⟪v, u⟫) • f v
-- 其中 𝐞 x = exp(2πIx)
```

### W21 范数
```lean
-- W21 范数定义
noncomputable def w21norm (f : W21) : ℝ :=
  (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
```

## 关键定理

### fourier_deriv
```lean
-- Fourier 变换的导数公式
-- 𝓕(deriv f) = (2πIu) • 𝓕(f)
theorem fourier_deriv
    {f : ℝ → E} (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x)
```

### fourierIntegral_self_add_deriv_deriv
```lean
-- (1+u²) * 𝓕(f) = 𝓕(f - 1/(4π²) * f'')
-- 已证明
theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u
```

### decay_bounds_key
```lean
-- Fourier 衰减估计
-- ‖𝓕(f) u‖ ≤ w21norm * (1+u²)⁻¹
-- 已证明
lemma decay_bounds_key (f : W21) (u : ℝ) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ f.w21norm * (1 + u ^ 2)⁻¹
```

### decay_bounds_cor
```lean
-- CS 函数的 Fourier 衰减
-- ∃ C, ∀ u, ‖𝓕(ψ) u‖ ≤ C/(1+u²)
-- 已证明
lemma decay_bounds_cor (ψ : CS 2 ℂ) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2)
```

### decay_bounds_W21
```lean
-- W21 函数的 Fourier 衰减 (带常数)
-- ‖𝓕(f) u‖ ≤ (π + 1/(4π)) * A / (1+u²)
-- 待证明
lemma decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2)
```

## 证明技巧

### 二阶导数处理
```lean
-- deriv^[2] f = deriv (deriv f)
-- 证明: rw [← iteratedDeriv_eq_iterate (n := 2), iteratedDeriv_succ, iteratedDeriv_one]
```

### Cast 处理
```lean
-- 1/(4*↑π²) = ↑(1/(4*π²))
-- 证明: push_cast; ring
```

### 常数提取
```lean
-- 1/(4π²) * ∫‖f''‖ ≤ A/(4π)
-- 步骤:
-- 1. mul_le_mul_of_nonneg_left h_int_f'' (by positivity)
-- 2. rw [show (1/(4π²)) * (π*A) = A/(4π) from by field_simp; ring_nf]
```

## 相关 Mathlib 模块

- `Mathlib.Analysis.Fourier.FourierTransform` - Fourier 变换定义
- `Mathlib.Analysis.Fourier.FourierTransformDeriv` - Fourier 变换导数
- `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` - Riemann-Lebesgue 引理
- `Mathlib.NumberTheory.Chebyshev` - Chebyshev 函数
