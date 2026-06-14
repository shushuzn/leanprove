# 困难 Proof 记录

## nnabla_mul_log_sq (line 503)

**类型**: BigO渐近分析证明

**目标**: `x*(a + log²(x/b)) - (x-1)*(a + log²((x-1)/b)) = O(log²x)`

**证明思路**:
1. 展开: `a + log²(x/b) + (x-1)*(log²(x/b) - log²((x-1)/b))`
2. `a + log²(x/b) = O(log²x)` ✅ (子任务7a,7b,7c完成)
3. `(x-1)*(log²(x/b) - log²((x-1)/b)) = O(log²x)` ❌ (最难)

**子任务7d的证明策略**:
- 分解: `log²(x/b) - log²((x-1)/b) = (log(x/b) - log((x-1)/b)) * (log(x/b) + log((x-1)/b))`
- `log(x/b) - log((x-1)/b) = log(x/(x-1))` ✅ (用 conv_lhs => rw [h_diff])
- `|log(x/(x-1))| = log(x/(x-1))` ✅ (用 rw [abs_of_pos ...])
- `|log(x/b) + log((x-1)/b)| ≤ 2|log x| + 2|log b|` ✅ (用 convert_to + norm_add_le)
- `log(x/(x-1)) ≤ 2/(x-1)` ✅ (用 log_le_sub_one_of_pos + div_sub_one)
- 组合: `(x-1) * 2/(x-1) * (2|log x| + 2|log b|) = 4|log x| + 4|log b|` ✅

**关键困难**: `rw [← Real.norm_eq_abs]` 在 `have` 内部会改写主目标中的 `|...|` 为 `‖...‖`，导致后续 `linarith` 看到 `⊢ False`。

**解决方案**:
1. 用 `convert_to` + `congr_arg₂` 代替 `rw` 来替换等式
2. 用 `rw [Real.norm_eq_abs] at this` 而不是 `rw [← Real.norm_eq_abs]`
3. 处理双重绝对值: `|(|a|)|` → `|a|` 用 `abs_of_nonneg (abs_nonneg _)`

**当前状态**: 所有子引理已证明，但组合步骤中 `rw [← Real.norm_eq_abs]` 的问题尚未完全解决。
