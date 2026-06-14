# 对数 (log) 相关 API

**Import**: `Mathlib.Analysis.SpecialFunctions.Pow.Real`（Real.log 系列）

## Real.log_div

**签名**:
```lean
Real.log_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x / y) = Real.log x - Real.log y
```
**Pitfall**: 需要 `x ≠ 0` 和 `y ≠ 0`，常用 `Ne.symm (ne_of_lt hb)` 从 `0 < b` 得到 `b ≠ 0`。

## Real.log_mul

**签名**:
```lean
Real.log_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x * y) = Real.log x + Real.log y
```

## Real.log_pos

**签名**:
```lean
Real.log_pos {x : ℝ} (hx : 1 < x) : 0 < Real.log x
```
**说明**: 用于证明 `x > e` 时 `log x > 1`（联合 `Real.exp_one_lt_three`）。

## Real.log_pos_iff

**签名**:
```lean
Real.log_pos_iff {x : ℝ} (hx : 0 ≤ x) : 0 < Real.log x ↔ 1 < x
```

## Real.log_le_sub_one_of_pos

**签名**:
```lean
Real.log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1
```
**说明**: 核心 bound：`log x ≤ x - 1`。用于证明 `log(x/(x-1)) ≤ 1/(x-1)`。

## Real.log_le_log

**签名**:
```lean
Real.log_le_log {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y
```

## Real.log_lt_log

**签名**:
```lean
Real.log_lt_log {x y : ℝ} (hx : 0 < x) (h : x < y) : Real.log x < Real.log y
```
**说明**: 证明 `log x > 1` 的核心步骤：`Real.log_exp 1 = 1`，所以 `exp 1 < x` 推出 `1 < log x`。

## Real.log_le_log_iff

**签名**:
```lean
Real.log_le_log_iff {x y : ℝ} (h : 0 < x) (h₁ : 0 < y) : Real.log x ≤ Real.log y ↔ x ≤ y
```

## Real.log_lt_log_iff

**签名**:
```lean
Real.log_lt_log_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x < Real.log y ↔ x < y
```

## 项目自定义 log BigO 引理

**Import**: `Leanprove.WienerProof`

| 引理 | 签名 |
|------|------|
| `log_add_div_isBigO_log a hb` | `log((x+a)/b) =O[atTop] log x` |
| `nabla_log hb` | `log((x+1)/b) - log(x/b) =O[atTop] 1/x` |
| `log_isbigo_log_div hb` | `log n =O[atTop] log(n/d)` |
| `log_sq_isbigo_mul hb` | `(log x)² =O[atTop] a + (log(x/b))²` |

## 常用 log bound 模式

**问题**: `|log(x/(x-1))| ≤ 2/(x-1)` 当 `x > 2`。
```lean
have h_div_pos : 0 < x / (x - 1) := div_pos (by linarith) (by linarith)
have h_gt1 : 1 < x / (x - 1) := by
  rw [one_lt_div (by linarith : 0 < x - 1)]
  linarith
have h_log_abs : |Real.log (x / (x - 1))| = Real.log (x / (x - 1)) :=
  abs_of_pos (Real.log_pos h_gt1)
have h_log_bound : Real.log (x / (x - 1)) ≤ 2 / (x - 1) := by
  have h := Real.log_le_sub_one_of_pos h_div_pos
  -- h: log(x/(x-1)) ≤ x/(x-1) - 1 = 1/(x-1)
  rw [div_sub_one (by linarith : x - 1 ≠ 0)] at h
  have h1 : 1 / (x - 1) ≤ 2 / (x - 1) := by
    refine (one_le_two.trans ?_).div_le_div_of_nonneg_right (by linarith)
  linarith
```

## 常用 log 恒等式

```lean
-- log(x/b) - log((x-1)/b) = log(x/(x-1))
rw [Real.log_div (by linarith) (Ne.symm (ne_of_lt hb))]
rw [Real.log_div (by linarith) (Ne.symm (ne_of_lt hb))]
rw [show log x - log b - (log(x-1) - log b) = log x - log(x-1) from by ring_nf]
rw [← Real.log_div (by linarith) (by linarith : x - 1 ≠ 0)]
```
