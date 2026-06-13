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
-- 解决方案:
have h := mul_le_mul_of_nonneg_left h_int_f'' (by positivity)
rw [show (1 / (4 * π ^ 2)) * (π * A) = A / (4 * π) from by field_simp; ring_nf] at h
exact h
```

## 代数恒等式模式

### `field_simp` 会关闭目标
```lean
-- 问题: field_simp 在 have 内部关闭目标，导致后续 rw 无法使用
-- 解决方案: 使用 field_simp + ring_nf 组合，或使用 mul_assoc 转换

-- 错误用法:
have h : ... := by field_simp; ring_nf  -- h 已被证明，无法 rw

-- 正确用法:
rw [show ... from by field_simp; ring_nf]  -- 直接在 rw 中使用
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
