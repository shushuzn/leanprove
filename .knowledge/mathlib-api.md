# Mathlib API 用法记录

## 积分相关

### integral_mono
```lean
-- 比较积分: ∫ f ≤ ∫ g 当 f ≤ g 点态
integral_mono (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ᵐ a ∂μ, f a ≤ g a)
```

### integral_add
```lean
-- 拆分积分: ∫ (f + g) = ∫ f + ∫ g
integral_add (hf : Integrable f μ) (hg : Integrable g μ)
```

### integral_mul_const
```lean
-- 提取常数: ∫ (f * c) = (∫ f) * c
integral_mul_const (c : ℝ) (f : α → ℝ)
-- 注意: 这是 ∫ f * c, 不是 ∫ c * f
-- 对于 ∫ c * f, 需要 rw [mul_comm] 转换
```

### integral_const_mul
```lean
-- 提取常数: ∫ (c * f) = c * ∫ f
integral_const_mul (c : ℝ) (f : α → ℝ)
```

### Integrable 相关
```lean
-- 范数可积
Integrable.norm (hf : Integrable f μ) : Integrable (fun x => ‖f x‖) μ

-- 标量乘法可积
Integrable.smul (c : 𝕜) (hf : Integrable f μ) : Integrable (c • f) μ

-- 常数乘法可积
Integrable.const_mul (c : 𝕜) (hf : Integrable f μ) : Integrable (fun x => c * f x) μ

-- 加法可积
Integrable.add (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (f + g) μ

-- 减法可积
Integrable.sub (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (f - g) μ

-- 用点态 bound 证明可积 (mono)
Integrable.mono (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ

-- 变量替换: f(a*x) 可积 ↔ f(x) 可积
integrable_comp_mul_left_iff (f : ℝ → F) {R : ℝ} (hR : R ≠ 0)
```

## Fourier 变换

### fourier_deriv
```lean
-- 𝓕(deriv f) = (2πIu) • 𝓕(f)
fourier_deriv (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x)
```

### fourierIntegral_continuous
```lean
-- L¹ 函数的 Fourier 变换连续
fourierIntegral_continuous (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {f : V → E} (hf : Integrable f μ) : Continuous (fourierIntegral e μ L f)
```

### norm_fourierIntegral_le_integral_norm
```lean
-- ‖𝓕(f)‖ ≤ ∫‖f‖
norm_fourierIntegral_le_integral_norm : ‖𝓕 f u‖ ≤ ∫ t, ‖f t‖
```

## ContDiff 相关

### ContDiff.continuous_deriv
```lean
-- C^n 函数的导数连续
ContDiff.continuous_deriv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Continuous (deriv f)
```

### ContDiff.deriv'
```lean
-- C^(n+1) 函数的导数是 C^n
ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n (deriv f)
```

### ContDiff.continuous_deriv_one
```lean
-- C^1 函数的导数连续
ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f) : Continuous (deriv f)
```

## HasCompactSupport 相关

### HasCompactSupport.deriv
```lean
-- 紧支集函数的导数也是紧支集
HasCompactSupport.deriv (hf : HasCompactSupport f) : HasCompactSupport (deriv f)
```

### integrable_of_hasCompactSupport
```lean
-- 紧支集连续函数可积
Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (h : HasCompactSupport f) : Integrable f
```

## norm 相关

### norm_sub_le
```lean
-- 三角不等式: ‖a - b‖ ≤ ‖a‖ + ‖b‖
norm_sub_le (a b : E) : ‖a - b‖ ≤ ‖a‖ + ‖b‖
```

### norm_mul
```lean
-- 范数乘法: ‖a * b‖ = ‖a‖ * ‖b‖
norm_mul (a b : 𝕜) : ‖a * b‖ = ‖a‖ * ‖b‖
```

### norm_real
```lean
-- 实数范数: ‖(↑x : ℂ)‖ = ‖x‖
norm_real (x : ℝ) : ‖(↑x : ℂ)‖ = ‖x‖
```

### Real.norm_eq_abs
```lean
-- 实数范数等于绝对值
Real.norm_eq_abs (x : ℝ) : ‖x‖ = |x|
```

## BigO / 渐近分析

### IsBigO.of_bound
```lean
-- 用常数 bound 证明 BigO
IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g
```

### IsBigO.add
```lean
-- BigO 加法: f₁ =O g → f₂ =O g → (f₁ + f₂) =O g
IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g
```

### IsBigO.pow
```lean
-- BigO 幂次: f =O g → f^n =O g^n
IsBigO.pow (h : f =O[l] g) (n : ℕ) : (fun x => f x ^ n) =O[l] (fun x => g x ^ n)
-- 对于 n=2: h.sq
```

### isLittleO_const_of_tendsto_atTop
```lean
-- 常数 =o g 当 g → ∞
isLittleO_const_of_tendsto_atTop (c : ℝ) (hg : Tendsto g atTop atTop) :
    (fun _ => c) =o[atTop] g
```

### log_add_div_isBigO_log
```lean
-- log(x + a / b) = O(log x)
log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x => Real.log (x + a / b)) =O[atTop] Real.log
-- 对于 log(x/b): 用 a = 0, 然后 simp only [add_zero]
```

### Real.log_div
```lean
-- log(x/y) = log x - log y
Real.log_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x / y) = Real.log x - Real.log y
```

### Real.log_pos
```lean
-- 1 < x → 0 < log x
Real.log_pos {x : ℝ} (hx : 1 < x) : 0 < Real.log x
```

### Real.log_le_sub_one_of_pos
```lean
-- log x ≤ x - 1 (for x > 0)
Real.log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1
```

### div_sub_one
```lean
-- x/y - 1 = (x - y) / y
div_sub_one {x y : ℝ} (hy : y ≠ 0) : x / y - 1 = (x - y) / y
```

### norm_add_le
```lean
-- ‖a + b‖ ≤ ‖a‖ + ‖b‖
norm_add_le (a b : E) : ‖a + b‖ ≤ ‖a‖ + ‖b‖
-- 对于 |a + b| ≤ |a| + |b|, 需要:
-- rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
```

### abs_sub
```lean
-- |a - b| ≤ |a| + |b|
abs_sub (a b : ℝ) : |a - b| ≤ |a| + |b|
```
