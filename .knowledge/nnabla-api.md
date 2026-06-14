# nnabla / nabla 序列差分 API

**Import**: `Leanprove.WienerProof`（项目自定义定义和引理）

## nabla

**签名**:
```lean
def nabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u (n + 1) - u n
```
**说明**: 正向差分。

## nnabla

**签名**:
```lean
def nnabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u n - u (n + 1)
```
**说明**: 负向差分，`nnabla u = -nabla u`。用于递减序列（`nnabla u n ≥ 0`）。

## neg_nabla

**签名**:
```lean
lemma neg_nabla [Ring E] {u : ℕ → E} : -(nabla u) = nnabla u := by
  ext n; simp [nabla, nnabla]
```

## nabla_mul / nnabla_mul

**签名**:
```lean
@[simp] lemma nabla_mul [Ring E] {u : ℕ → E} {c : E} : nabla (fun n => c * u n) = c • nabla u
@[simp] lemma nnabla_mul [Ring E] {u : ℕ → E} {c : E} : nnabla (fun n => c * u n) = c • nnabla u
```
**说明**: 常数乘法与差分交换。

## summation_by_parts

**签名**:
```lean
lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} : ...
```
**说明**: Abel 分部求和公式。

## cumsum_summation

**签名**:
```lean
lemma cumsum_summation ... (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b)
```
**说明**: 通过差分证明级数可和。

## nnabla BigO bound 模式

**说明**: 对于递减序列 `u`，`|nnabla u n| = u n - u (n+1) ≤ u n`，可转为 BigO 证明。
**Pitfall**: 绝对值简化 `rw [abs_of_nonneg (sub_nonneg.mpr h_decr)]` 可能失败，需用其他方法。

```lean
-- 标准模式: 证明 u 递减 → u n - u (n+1) ≤ u n → |nnabla u n| ≤ |u n|
apply IsBigO.of_bound 1
filter_upwards [eventually_gt_atTop 3] with n hn
simp only [nnabla, norm_eq_abs, one_mul]
-- 然后证明 |u n - u (n+1)| ≤ |u n|
```
