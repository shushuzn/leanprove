# nnabla_bound_aux 子任务证明要点

## 目标
```lean
nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
(fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2))
```

## 子任务分解

### 8a. 证明 u n = 1 / (n * ((2π)² + log(n/x)²)) 递减
- 等价于: `(n+1) * ((2π)² + log((n+1)/x)²) ≥ n * ((2π)² + log(n/x)²)`
- 因为 `n+1 > n` 且 `log((n+1)/x) ≥ log(n/x)`（当 n ≥ x）
- 关键API: `Real.log_le_log` (单调性), `Nat.cast_le`, `mul_le_mul_of_nonneg_left`
- 需要条件: `n ≥ x` 或更弱的 `0 < x`

### 8b. 证明 nnabla u n = u n - u (n+1) ≤ 0
- 这是 8a 的推论: `u n ≥ u (n+1)` 所以 `u n - u (n+1) ≥ 0`
- 即 `nnabla u n ≥ 0`
- API: 直接从 8a 推出

### 8c. 证明 |nnabla u n| = nnabla u n
- 因为 8b 中 `nnabla u n ≥ 0`，所以 `|nnabla u n| = nnabla u n`
- API: `abs_of_nonneg`

### 8d. 证明 nnabla u n ≤ 1 / ((n+1) * log((n+1)/x)²)
- 关键: `u n ≤ 1/(n * log(n/x)²)`（去掉 (2π)²）
- 所以 `nnabla u n = u n - u (n+1) ≤ u n ≤ 1/(n * log(n/x)²)`
- 进一步: `1/(n * log(n/x)²) ≤ 1/((n+1) * log((n+1)/x)²)`? 不一定
- 实际上: `u n - u (n+1) ≤ u n`，但需要更紧的 bound
- 更直接: `nnabla u n ≤ 1/((n+1) * ((2π)² + log((n+1)/x)²)) ≤ 1/((n+1) * log((n+1)/x)²)`

### 8e. 证明 1/((n+1) * log((n+1)/x)²) ≤ 1/(n² * log n²)
- 关键: `(n+1) * log((n+1)/x)² ≥ n² * log n²`
- 这可能不对！需要更紧的 bound
- 实际证明可能用 `IsBigO.of_bound 1` + `nnabla u n ≤ 1/((n+1)*log((n+1)/x)²) ≤ ...`

## 替代策略

### 策略 A: 直接用 IsBigO.of_bound 1
- 目标: `|nnabla u n| ≤ 1 / (n² * log n²)` 当 n 足够大
- 关键: `u n ≤ 1/(n * log(n/x)²)` 且 `u (n+1) ≥ 0`
- 所以 `nnabla u n = u n - u (n+1) ≤ u n ≤ 1/(n * log(n/x)²)`
- 需要: `1/(n * log(n/x)²) ≤ 1/(n² * log n²)`
- 即: `n * log n² ≤ n² * log(n/x)²`
- 即: `log n² ≤ n * log(n/x)²`
- 当 n 大时, RHS ~ n * (log n)² >> (log n)² = LHS, 所以成立

### 策略 B: 用 nnabla_mul 和已知引理
- `nnabla (fun n => 1 / (n * ((2π)² + log(n/x)²)))` 分解为 nnabla_mul
- 但这要求 `nnabla (fun n => 1/n)` 和 `nnabla (fun n => 1/((2π)² + log(n/x)²))` 已知

### 策略 C: 用 Mean Value Theorem
- `u n - u (n+1) = -u'(ξ)` 对某个 ξ ∈ (n, n+1)
- `u'(x) = -1/(x² * ((2π)² + log(x/x)²)) - x * 2log(x/x)/(x * ((2π)² + log(x/x)²)²)`
- 复杂但理论上可行

## 推荐路径

1. 证明 8a: u 递减（用 Real.log_le_log）
2. 证明 8b: nnabla u n ≥ 0
3. 证明 8c: |nnabla u n| = nnabla u n
4. 证明 8d: nnabla u n ≤ u n ≤ 1/(n * log(n/x)²)
5. 证明 8e: 1/(n * log(n/x)²) = O(1/(n² * log n²))
6. 组合到主文件

## 实际可能失败的点

- 8d 中的不等式 `nnabla u n ≤ u n` 平凡（因为 u (n+1) ≥ 0）
- 8e 需要 log n ≥ log(n/x) - log x，对于 x > 1 需要 log n ≥ log n - log x = log(n/x)，对
- 关键: `(n+1) * log((n+1)/x)² ≥ n² * log n²` 可能不对，因为 log n² 是关于 n 的
- 实际可能需要 `nnabla u n ≤ 1/(n * log n²)` 然后用 `IsBigO` 的传递性

## 备用方案

如果上述都不行，参考 `nnabla_bound` 的证明模式：
- `field_simp` 简化
- 用 `nnabla_mul` 分解
- 组合已知 BigO 引理

但这需要 `nnabla_bound_aux` 已经证明。