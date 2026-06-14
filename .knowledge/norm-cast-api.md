# 范数 / Cast 处理 API

## 范数转换

**Import**: `Mathlib.Analysis.NormedSpace.Basic`

| 引理 | 签名 | 作用 |
|------|------|------|
| `Real.norm_eq_abs` | `‖x‖ = |x|` （`x : ℝ`） | 实数范数→绝对值 |
| `norm_real` | `‖(↑x : ℂ)‖ = ‖x‖` | 复数范数→ℝ 范数 |
| `norm_mul` | `‖a * b‖ = ‖a‖ * ‖b‖` | 范数乘法 |
| `norm_add_le` | `‖a + b‖ ≤ ‖a‖ + ‖b‖` | 三角不等式 |
| `norm_sub_le` | `‖a - b‖ ≤ ‖a‖ + ‖b‖` | 减法三角不等式 |
| `abs_sub` | `|a - b| ≤ |a| + |b|` | 绝对值减法（`a b : ℝ`） |

## 范数处理标准模式

```lean
-- ‖(↑c : ℂ) * f‖ = c * ‖f‖ (当 c > 0)
rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

-- ‖(↑(1+u²) : ℂ)‖ = 1+u²
rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

## |a + b| ≤ |a| + |b|（norm_add_le 转换）

```lean
have h : |a + b| ≤ |a| + |b| := by
  have h_raw := norm_add_le a b      -- ‖a + b‖ ≤ ‖a‖ + ‖b‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
  exact h_raw
-- ⚠️ 不要用 rw [← Real.norm_eq_abs]（在 have 内部会影响主目标）
```

## Cast 处理

| 操作 | 方法 |
|------|------|
| `ℝ → ℂ` cast | `push_cast` / `norm_cast` |
| 除法等式 | `field_simp`（⚠️ 在 `show ... from by` 内部会关闭目标） |
| 环等式 | `ring_nf`（Nat 截断减法不适用） |

```lean
-- 1/(4*↑π²) = ↑(1/(4*π²))
have h_cast : (1 / (4 * (↑π : ℂ) ^ 2) : ℂ) = (↑(1 / (4 * π ^ 2) : ℝ) : ℂ) := by
  push_cast; ring
```

## 绝对值处理 pitfall

```lean
-- 问题: |log(x/b)²| = log(x/b)² 因为平方非负
-- ❌ 错误: rw [abs_of_nonneg (sq_nonneg _)]  -- 在 h1 中可能不匹配
-- ✅ 正确: 先提取为 have
have h_sq : |Real.log (x / b) ^ 2| = Real.log (x / b) ^ 2 := abs_of_nonneg (sq_nonneg _)
rw [h_sq] at h1
```

## 常用不等式

```lean
-- |a - b| ≤ |a| + |b|
have h := abs_sub a b

-- a - b ≤ a 当 b ≥ 0
sub_le_self {a b : ℝ} (h : 0 ≤ b) : a - b ≤ a
```
