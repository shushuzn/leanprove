# 可微性 / 连续性 API

## ContDiff 系列

**Import**: `Mathlib.Analysis.Calculus.ContDiff`

| 引理 | 作用 |
|------|------|
| `ContDiff.continuous_deriv h hn` (`1 ≤ n`) | C^n 函数的导数连续 |
| `ContDiff.deriv' h` (`h : ContDiff 𝕜 (n+1) f`) | C^(n+1) 函数的导数是 C^n |
| `ContDiff.continuous_deriv_one h` (`h : ContDiff 𝕜 1 f`) | C^1 函数的导数连续 |

## HasCompactSupport 系列

**Import**: `Mathlib.Topology.Support`

| 引理 | 作用 |
|------|------|
| `HasCompactSupport.deriv hf` | 紧支集函数的导数也是紧支集 |
| `Continuous.integrable_of_hasCompactSupport hf h` | 紧支集连续函数可积 |
| `ContDiff.integrable_of_hasCompactSupport hf h` | 紧支集 C^n 函数可积 |

## CS → W21 嵌入模式

**说明**: CS 函数（C² 紧支集）可嵌入 W21 空间。
```lean
let f : W21 := {
  toFun := ψ, smooth := ψ.h1,
  integrable := by
    intro k hk; interval_cases k
    · exact h_int  -- Integrable ψ
    · simp [iteratedDeriv_succ]; exact h_int'  -- Integrable (deriv ψ)
    · simp [iteratedDeriv_succ]; exact h_int''  -- Integrable (deriv² ψ)
}
-- CS 导数可积:
-- 一阶: (ψ.h1.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport ψ.h2.deriv
-- 二阶: (ψ.h1.deriv'.continuous_deriv_one).integrable_of_hasCompactSupport ψ.h2.deriv.deriv
```

## 积分三角不等式模式

**Import**: `Mathlib.MeasureTheory.Integral.Integral` / `Mathlib.Analysis.NormedSpace.Basic`
**说明**: 积分版的三角不等式 `∫‖f - c*g‖ ≤ ∫‖f‖ + c*∫‖g‖` 需要三步：
```lean
-- 1. 点态 bound: ∀ v, ‖f v - c*g v‖ ≤ ‖f v‖ + c*‖g v‖
-- 2. LHS 可积: Integrable (fun v => ‖f v - c*g v‖)
-- 3. RHS 可积: Integrable (fun v => ‖f v‖ + c*‖g v‖)
-- 4. integral_mono
-- 5. 拆分 RHS: integral_add + integral_mul_const
```

## norm_add_le 用于实数绝对值

**Import**: `Mathlib.Analysis.NormedSpace.Basic`
**说明**: `norm_add_le` 给出 `‖a + b‖ ≤ ‖a‖ + ‖b‖`，需转成实数绝对值。
```lean
have h : |a + b| ≤ |a| + |b| := by
  have h_raw := norm_add_le a b      -- ‖a + b‖ ≤ ‖a‖ + ‖b‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
  exact h_raw
-- ⚠️ 不要用 rw [← Real.norm_eq_abs]（会影响主目标）
```
