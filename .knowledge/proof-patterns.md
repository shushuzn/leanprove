# 证明模式与 Pitfalls

## field_simp 在 show/have 内部关闭目标

**Pitfall**: `field_simp` 在 `show ... from by` 内部会关闭目标，后续 `ring_nf` 报 "No goals to be solved"。
```lean
-- ❌ 错误
rw [show a = b from by field_simp; ring_nf]  -- ring_nf 多余
-- ✅ 正确: 分步写
rw [show a = b from by field_simp]
rw [show b = c from by ring_nf]
```

## rw [← X] 在 have 内部影响主目标

**Pitfall**: `rw [← Real.norm_eq_abs]` 在 `have` 内部会改写主目标中的 `|...|` 为 `‖...‖`，导致后续 `linarith` 看到 `⊢ False`。
**解决方案**:
1. 用 `rw [Real.norm_eq_abs] at this`（安全），不要用 `←`
2. 用 `convert_to + congr_arg₂` 代替 `rw`
3. `linarith` 显式传递假设

```lean
-- ✅ 安全
have h_raw := norm_add_le a b
rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw

-- ✅ 替代方案: convert_to
convert_to |f' x + g' x| ≤ C using 1
· exact congr_arg₂ (fun a b => |a + b|) h_eq1 h_eq2
```

## linarith 在 filter_upwards 内部看不到假设

**Pitfall**: 在 `filter_upwards` + `have` 上下文中，`linarith` 可能看不到某些假设。
```lean
-- ❌ 失败
linarith
-- ✅ 成功
linarith [h1, h2, h3, h4]
```

## Integrable.smul 类型推断卡住

**Pitfall**: Lean 无法推断标量类型。
```lean
-- ❌ 错误
exact (W21.hf'' f).smul _
-- ✅ 正确: 显式提供标量类型
exact (W21.hf'' f).smul (↑c : ℂ)
```

## integral_mul_const vs integral_const_mul

```lean
-- integral_mul_const: ∫ (f * c) = (∫ f) * c
-- integral_const_mul: ∫ (c * f) = c * ∫ f
-- 通过 mul_comm 转换:
rw [show (fun v => c * ‖f v‖) = (fun v => ‖f v‖ * c) from by ext v; rw [mul_comm]]
rw [integral_mul_const]; rw [mul_comm]
```

## atTop vs Filter.atTop 类型不匹配

**Pitfall**: `simp` 可能将 `atTop` 变为 `Filter.atTop`，导致 BigO filter 类型不匹配。
**解决**: 避免在 BigO 证明中用 `simp` 改写目标。

## div_pos 需要显式类型

**Pitfall**: `div_pos (by linarith) hx1` 在 `have` 内部会失败。
**解决**: 显式提供类型。
```lean
div_pos (by linarith : 0 < x) hx1
```

## (a*b)*c = d 的拆解模式

```lean
-- 目标: (1/(4π²)) * (π * A) = A/(4π)
rw [← mul_assoc]  -- 变成 ((1/(4π²)) * π) * A
rw [show (1/(4π²)) * π = 1/(4π) from by field_simp]
rw [show A/(4π) = 1/(4π) * A from by ring_nf]
exact h
```

## mul_inv_cancel_left₀ 模式

```lean
-- (x-1) * (1/(x-1)) = 1
rw [mul_inv_cancel_left₀ (by linarith : x - 1 ≠ 0)]
```

## Real.exp_one_lt_three

**Import**: `Mathlib.Analysis.Complex.ExponentialBounds`
```lean
Real.exp_one_lt_three : exp 1 < 3
```
**说明**: 用于 `eventually_gt_atTop 3` 的 bound（因为 `e < 3`）。
