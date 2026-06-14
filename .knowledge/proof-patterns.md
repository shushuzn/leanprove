# 证明模式和技巧

## Cast 处理模式

### 问题: `1/(4*↑π²)` vs `↑(1/(4*π²))`
```lean
-- 解决方案: 使用 push_cast + ring
have h_cast : (1 / (4 * (↑π : ℂ) ^ 2) : ℂ) = (↑(1 / (4 * π ^ 2) : ℝ) : ℂ) := by
  push_cast; ring
```

### 问题: `‖↑(1+u²)‖` vs `1+u²`
```lean
-- 解决方案: norm_real + abs_of_pos
have h_norm : ‖(↑(1 + u ^ 2 : ℝ) : ℂ)‖ = (1 + u ^ 2 : ℝ) := by
  rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

### 问题: `‖↑c * f‖` vs `c * ‖f‖`
```lean
-- 解决方案: norm_mul + norm_real + abs_of_pos
have h : ‖(↑c : ℂ) * f‖ = c * ‖f‖ := by
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

## 积分不等式模式

### 三角不等式积分
```lean
-- 目标: ∫‖f - c*g‖ ≤ ∫‖f‖ + c*∫‖g‖
-- 步骤:
-- 1. 点态 bound: ‖f v - c*g v‖ ≤ ‖f v‖ + c*‖g v‖
-- 2. LHS 可积: Integrable (fun v => ‖f v - c*g v‖)
-- 3. RHS 可积: Integrable (fun v => ‖f v‖ + c*‖g v‖)
-- 4. integral_mono
-- 5. RHS 拆分: integral_add + integral_mul_const
```

### 常数提取
```lean
-- 问题: 1/(4π²) * ∫‖f''‖ ≤ A/(4π)
-- 步骤:
-- 1. mul_le_mul_of_nonneg_left h_int_f'' (by positivity)
-- 2. rw [← mul_assoc]  -- 把 (1/(4π²)) * (π*A) 变成 ((1/(4π²)) * π) * A
-- 3. rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp]  -- field_simp 关闭等式
-- 4. rw [show A / (4 * π) = 1 / (4 * π) * A from by ring_nf]  -- mul_comm
-- 5. exact h
```

### 代数恒等式: `1/(4π²) * π = 1/(4π)`
```lean
-- field_simp 可以直接关闭此等式
-- 不需要 ring_nf 跟在后面
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp]
```

## 代数恒等式模式

### `field_simp` 在 `show` 内部会关闭目标
```lean
-- 问题: field_simp 在 show 内部关闭目标，导致 rw 无法使用
-- 错误: "No goals to be solved"

-- 解决方案1: 使用 mul_assoc + ring_nf 组合
rw [show (1 / (4 * π ^ 2)) * (π * A) = (1 / (4 * π ^ 2) * π) * A from by ring_nf]
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp; ring_nf]
ring_nf

-- 解决方案2: 直接使用 rw 而不是 show
rw [← mul_assoc]
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp; ring_nf]
```

### `(4*π²)⁻¹` vs `1/(4*π²)`
```lean
-- 这两个是相等的，但 Lean 不认为它们 definitionally equal
-- 解决方案: rw [show (4 * π ^ 2)⁻¹ = 1 / (4 * π ^ 2) from by ring_nf]
```

## Fourier 变换证明模式

### 线性性
```lean
-- 𝓕(f + g) = 𝓕(f) + 𝓕(g)
F_add (hf : Integrable f) (hg : Integrable g) (x : ℝ)

-- 𝓕(c * f) = c * 𝓕(f)
F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ}
```

### 导数公式
```lean
-- 𝓕(deriv f) = (2πIu) * 𝓕(f)
fourier_deriv (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f))
```

### 二阶导数
```lean
-- deriv^[2] f = deriv (deriv f)
-- 证明: rw [← iteratedDeriv_eq_iterate (n := 2), iteratedDeriv_succ, iteratedDeriv_one]
```

## W21 相关模式

### CS → W21 嵌入
```lean
-- CS 函数是 C² 紧支集，可嵌入 W21
let f : W21 := {
  toFun := ψ
  smooth := ψ.h1
  integrable := by
    intro k hk
    interval_cases k
    · exact h_int  -- Integrable ψ
    · simp [iteratedDeriv_succ]; exact h_int'  -- Integrable (deriv ψ)
    · simp [iteratedDeriv_succ]; exact h_int''  -- Integrable (deriv (deriv ψ))
}
```

### CS 函数导数可积
```lean
-- 一阶导数
(ψ.h1.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport ψ.h2.deriv

-- 二阶导数
(ψ.h1.deriv'.continuous_deriv_one).integrable_of_hasCompactSupport ψ.h2.deriv.deriv
```

## BigO 渐近分析模式

### IsBigO.of_bound + filter_upwards
```lean
-- 目标: f =O[atTop] g
-- 步骤:
-- 1. apply IsBigO.of_bound C  -- C 是常数
-- 2. filter_upwards [eventually_gt_atTop N] with x hx
-- 3. simp only [norm_eq_abs, one_mul]  -- 转换 ‖‖ 到 |...|
-- 4. 处理双重 |...|: rw [abs_of_nonneg (abs_nonneg _)]
-- 5. 处理 |a²|: rw [abs_of_nonneg (sq_nonneg _)]
-- 6. 处理 |a*b|: rw [abs_mul]
-- 7. 处理 |a| when a > 0: rw [abs_of_pos h]
```

### log 恒等式
```lean
-- log(x/b) = log x - log b
Real.log_div hx' hb' : Real.log (x / b) = Real.log x - Real.log b

-- log(x/(x-1)) = log x - log(x-1)
Real.log_div hx' hx1' : Real.log (x / (x - 1)) = Real.log x - Real.log (x - 1)

-- log(x/b) = O(log x)
log_add_div_isBigO_log 0 hb : (fun x => Real.log (x + 0 / b)) =O[atTop] Real.log
-- 需要 simp only [add_zero] 来简化

-- a²-b² = (a-b)(a+b)
-- 用 ring_nf 证明
```

### BigO 组合
```lean
-- IsBigO.add: f₁ =O g → f₂ =O g → (f₁ + f₂) =O g
-- IsBigO.mul: f₁ =O g₁ → f₂ =O g₂ → (f₁ * f₂) =O (g₁ * g₂)
-- IsBigO.pow: f =O g → f^n =O g^n
-- isLittleO_const_of_tendsto_atTop: const =o g when g → ∞
```

### rw 在 filter_upwards 上下文中的行为
```lean
-- 问题: rw [← Real.norm_eq_abs] 在 have 内部会影响主目标
-- 解决方案:
--   1. 用 convert_to + congr_arg₂ 代替 rw
--   2. 用 rw [Real.norm_eq_abs] at this (安全，不影响主目标)
--   3. linarith 需要显式传递假设: linarith [h1, h2, h3, h4]

-- convert_to 用法:
convert_to new_goal using 1
· exact congr_arg₂ (fun a b => |a + b|) eq1 eq2

-- norm_add_le 转换:
have h_raw := norm_add_le a b
rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
-- h_raw : |a + b| ≤ |a| + |b|
```
