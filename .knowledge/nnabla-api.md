# nnabla / nabla 序列差分 API

## 基础定义

### nabla
```lean
-- 正向差分
def nabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u (n + 1) - u n
```

### nnabla
```lean
-- 负向差分（项目自定义）
def nnabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u n - u (n + 1)
-- 即 nnabla u = -nabla u
```

## 关键引理

### neg_nabla
```lean
lemma neg_nabla [Ring E] {u : ℕ → E} : -(nabla u) = nnabla u := by
  ext n; simp [nabla, nnabla]
```

### nabla_mul / nnabla_mul
```lean
-- 常数乘法与差分交换
@[simp] lemma nabla_mul [Ring E] {u : ℕ → E} {c : E} : nabla (fun n => c * u n) = c • nabla u
@[simp] lemma nnabla_mul [Ring E] {u : ℕ → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u
```

### summation_by_parts
```lean
-- Abel 求和（分部求和）
lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    ...
```

### cumsum_summation
```lean
-- 通过差分证明级数可和
lemma cumsum_summation ...
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b)
```

## 在 nnabla_bound_aux 中的应用

### 目标
```lean
nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
(fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2))
```

### 关键观察
- `u n = 1 / (n * ((2π)² + log(n/x)²))` 是递减的（当 n 大时）
- 所以 `nnabla u n = u n - u (n+1) ≤ 0`
- 因此 `|nnabla u n| = u (n+1) - u n`
- `u (n+1) - u n ≤ 1 / ((n+1) * log((n+1)/x)²)`
- 而 `1 / ((n+1) * log((n+1)/x)²) ≤ 1 / (n * log n²)`

### 证明策略
1. 证明 u 递减（用 `Real.log` 单调性 + n+1 > n）
2. 展开 nnabla 为 u n - u (n+1)
3. 用 `Real.log_le_sub_one_of_pos` 或类似不等式 bound 差
4. 用 `IsBigO.of_bound` 组合

## 相关 BigO 技巧

### nnabla 与 BigO
```lean
-- nnabla u = u n - u (n+1) 可以展开为 nabla 的负数
-- 如果 |u n| 和 |u (n+1)| 都是 O(g)，则 |nnabla u n| = O(g)
```

### 经验
- 序列 u 递减时 `nnabla u n ≥ 0`
- `nnabla (f * g) = f n * nnabla g + nnabla f * g (n+1)`（待验证）