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
-- ⚠️ 注意参数顺序: hg(大函数) → hf(AEStronglyMeasurable) → h(bound)
theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ
-- 用法: hf_int.mono h_ae h_bound

-- 变量替换: f(a*x) 可积 ↔ f(x) 可积
integrable_comp_mul_left_iff (f : ℝ → F) {R : ℝ} (hR : R ≠ 0)
```

### AEStronglyMeasurable 相关
```lean
-- 连续函数是 AEStronglyMeasurable
Continuous.aestronglyMeasurable (hf : Continuous f) : AEStronglyMeasurable f μ

-- smul 组合: AEStronglyMeasurable (c • f) 当 c 和 f 都 AEStronglyMeasurable
AEStronglyMeasurable.smul (hc : AEStronglyMeasurable c μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => c x • f x) μ
-- 用法: 来自 Mathlib/Analysis/Fourier/Inversion.lean:63
-- AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop)) hf.1
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

---

## 常用 Lean 4 技巧（来自 skill）

### Cast处理
- `push_cast` / `norm_cast` 处理类型转换
- `field_simp` 处理除法等式（注意 pitfall：在 show 内部会关闭目标）
- `ring_nf` 处理环等式（Nat截断减法不适用）

### 范数处理
```lean
-- ‖(↑c : ℂ) * f‖ = c * ‖f‖ (当 c > 0)
rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

-- ‖(↑(1+u²) : ℂ)‖ = 1+u²
rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

### 积分相关
- `integral_mono` 比较积分（需要 LHS/RHS 可积）
- `integral_add` 拆分积分（需要两个可积函数）
- `integral_mul_const` 提取常数（注意方向）
- `Integrable.norm` 范数可积
- `Integrable.smul` 标量乘法可积（显式提供标量类型）
- `Integrable.const_mul` 常数乘法可积
- `Integrable.of_le` 用点态 bound 证明可积

### ContDiff 相关
- `ContDiff.continuous_deriv` C^n 函数导数连续
- `ContDiff.deriv'` C^(n+1) → C^n 导数
- `ContDiff.continuous_deriv_one` C^1 导数连续
- `HasCompactSupport.deriv` 紧支集导数也是紧支集

### CS → W21 嵌入模式
```lean
-- CS 函数 (C² 紧支集) 可嵌入 W21
let f : W21 := {
  toFun := ψ, smooth := ψ.h1,
  integrable := by
    intro k hk; interval_cases k
    · exact h_int  -- Integrable ψ (from compact support + continuous)
    · simp [iteratedDeriv_succ]; exact h_int'  -- Integrable (deriv ψ)
    · simp [iteratedDeriv_succ]; exact h_int''  -- Integrable (deriv² ψ)
}
-- CS 导数可积:
-- 一阶: (ψ.h1.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport ψ.h2.deriv
-- 二阶: (ψ.h1.deriv'.continuous_deriv_one).integrable_of_hasCompactSupport ψ.h2.deriv.deriv
```

### Fourier变换
- `fourier_deriv`: 𝓕(deriv f) = (2πIu) • 𝓕(f)
- `fourierIntegral_continuous`: L¹函数的Fourier变换连续
- `norm_fourierIntegral_le_integral_norm`: ‖𝓕(f)‖ ≤ ∫‖f‖
- `decay_bounds_key`: ‖𝓕(f) u‖ ≤ w21norm * (1+u²)⁻¹

### BigO/渐近分析
```lean
-- 显式常数 bound
IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g

-- 组合两个 BigO
IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g

-- 常数 = o(g) 当 g → ∞
isLittleO_const_of_tendsto_atTop (c : ℝ) (hg : Tendsto g atTop atTop) : (fun _ => c) =o[atTop] g

-- o(g) ⊂ O(g)
IsLittleO.isBigO (h : f =o[l] g) : f =O[l] g

-- BigO 平方
Asymptotics.IsBigO.sq (h : f =O[l] g) : (fun x => f x ^ 2) =O[l] (fun x => g x ^ 2)

-- log 渐近引理 (项目特定)
log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x
nabla_log {b : ℝ} (hb : 0 < b) :
    (fun x => Real.log ((x + 1) / b) - Real.log (x / b)) =O[atTop] fun x => 1 / x
log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d))
log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2)
```

### ⚠️ atTop vs Filter.atTop 类型不匹配
```lean
-- 问题: simp 可能将 atTop 变为 Filter.atTop，导致类型不匹配
-- h : f =O[Filter.atTop] g  -- simp 后
-- goal: f =O[atTop] g        -- 原始
-- 解决方案: 避免在 BigO 证明中用 simp 改写目标
```

### ⚠️ abs_of_nonneg (sq_nonneg _) 用于平方的绝对值
```lean
-- 问题: |log(x/b)²| = log(x/b)² 因为平方非负
-- ❌ 错误: rw [abs_of_nonneg (sq_nonneg _)]  -- 在 h1 中可能不匹配
-- ✅ 正确: 先提取为 have，再 rw
have h_sq : |Real.log (x / b) ^ 2| = Real.log (x / b) ^ 2 := abs_of_nonneg (sq_nonneg _)
rw [h_sq] at h1
```

### ⚠️ log_div 恒等式
```lean
-- log(x/b) - log((x-1)/b) = log(x/(x-1))
-- 步骤:
-- 1. rw [Real.log_div (by linarith) (Ne.symm (ne_of_lt hb))]
-- 2. rw [Real.log_div (by linarith) (Ne.symm (ne_of_lt hb))]
-- 3. rw [show log x - log b - (log(x-1) - log b) = log x - log(x-1) from by ring_nf]
-- 4. rw [← Real.log_div (by linarith) (by linarith : x - 1 ≠ 0)]
```

### ⚠️ mul_inv_cancel_left₀ 模式
```lean
-- (x-1) * (1/(x-1)) = 1
-- 用 field_simp 或 rw [mul_inv_cancel_left₀ (by linarith : x - 1 ≠ 0)]
```

### Integrable.mono 完整模式
```lean
-- 证明 f 可积，通过 g 可积 + ‖f‖ ≤ ‖g‖ 点态
-- 步骤:
-- 1. 证明 h_bound: ∀ u, ‖f u‖ ≤ g u
-- 2. 证明 h_int: Integrable g
-- 3. 证明 h_meas: AEStronglyMeasurable f (用 comp_measurable 模式)
-- 4. 证明 h_bound': ∀ᵐ u, ‖f u‖ ≤ ‖g u‖ (用 Filter.Eventually.of_forall + abs_of_nonneg)
-- 5. exact h_int.mono h_meas h_bound'

-- AEStronglyMeasurable via comp_measurable:
have h_meas : AEStronglyMeasurable f volume := by
  apply (continuous_f).aestronglyMeasurable.comp_measurable
  exact measurable_g  -- e.g., measurable_id.div_const c
```

### 变量替换: integrable_comp_mul_left_iff
```lean
-- f(a*x) 可积 ↔ f(x) 可积 (当 a ≠ 0)
-- 用法:
rw [show (fun u => f (c⁻¹ * u)) = (fun u => f (c⁻¹ * u)) from by ext u; rfl]
rw [integrable_comp_mul_left_iff f (inv_ne_zero hc)]
exact integrable_f
```

### ⚠️ filter_upwards 内部 rw 行为
```lean
-- rw [← Real.norm_eq_abs] 在 have 内部会影响主目标
-- 解决方案: 用 convert_to + congr_arg₂ 或 rw [Real.norm_eq_abs] at this
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

## Log 相关

### Real.log_div
```lean
-- log(x/y) = log x - log y
Real.log_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x / y) = Real.log x - Real.log y
```

### Real.log_mul
```lean
-- log(x*y) = log x + log y
Real.log_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x * y) = Real.log x + Real.log y
```

### Real.log_pos
```lean
-- 1 < x → 0 < log x
Real.log_pos {x : ℝ} (hx : 1 < x) : 0 < Real.log x
```

### Real.log_pos_iff
```lean
-- 0 ≤ x → (0 < log x ↔ 1 < x)
Real.log_pos_iff {x : ℝ} (hx : 0 ≤ x) : 0 < Real.log x ↔ 1 < x
```

### Real.log_le_sub_one_of_pos
```lean
-- log x ≤ x - 1 (for x > 0)
Real.log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1
```

### Real.log_le_log
```lean
-- 0 < x → x ≤ y → log x ≤ log y
Real.log_le_log {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y
```

### Real.log_lt_log
```lean
-- 0 < x → x < y → log x < log y
Real.log_lt_log {x y : ℝ} (hx : 0 < x) (h : x < y) : Real.log x < Real.log y
```

### Real.log_le_log_iff
```lean
-- 0 < x → 0 < y → (log x ≤ log y ↔ x ≤ y)
Real.log_le_log_iff {x y : ℝ} (h : 0 < x) (h₁ : 0 < y) : Real.log x ≤ Real.log y ↔ x ≤ y
```

### Real.log_lt_log_iff
```lean
-- 0 < x → 0 < y → (log x < log y ↔ x < y)
Real.log_lt_log_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x < Real.log y ↔ x < y
```

## 除法相关

### div_sub_one
```lean
-- a/b - 1 = (a - b) / b
div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b
```

### one_lt_div
```lean
-- 0 < b → (1 < a / b ↔ b < a)
one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
```

### div_lt_iff₀
```lean
-- 0 < c → (a / c < b ↔ a < b * c)
div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c
```

### lt_div_iff₀'
```lean
-- 0 < c → (a < b / c ↔ a * c < b)
lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ a * c < b
```

### div_le_div_of_nonneg_right
```lean
-- a ≤ b → 0 ≤ c → a / c ≤ b / c
div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
```

### sub_le_self
```lean
-- a - b ≤ a 当 b ≥ 0
sub_le_self {a b : ℝ} (h : 0 ≤ b) : a - b ≤ a
```
