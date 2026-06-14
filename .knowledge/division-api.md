# 除法相关 API

**Import**: `Mathlib.Algebra.Order.Field.Basic`

## div_sub_one

**签名**:
```lean
div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b
```
**说明**: 用于 `log(x/(x-1)) ≤ 1/(x-1)` 的 bound 推导。

## one_lt_div

**签名**:
```lean
one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
```
**说明**: 证明 `1 < x/(x-1)`（当 `x > 1` 时）。

## div_lt_iff₀

**签名**:
```lean
div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c
```

## lt_div_iff₀'

**签名**:
```lean
lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ a * c < b
```

## div_le_div_of_nonneg_right

**签名**:
```lean
div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
```
**说明**: 用于 `1/(x-1) ≤ 2/(x-1)` 等 bound。
