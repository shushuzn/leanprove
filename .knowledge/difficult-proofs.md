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

**关键困难**: 在 `filter_upwards` + `have` 上下文中，`linarith` 看到 `⊢ False` 而不是正确的目标。

**根因分析**:
1. `rw [← Real.norm_eq_abs]` 在 `have` 内部会影响主目标中的 `|...|` 为 `‖...‖`
2. 这导致主目标被意外修改，后续 `linarith` 看到 `⊢ False`
3. 独立测试中所有子引理都成功，说明问题在于组合上下文

**解决方案**:
1. 用 `convert_to` + `congr_arg₂` 代替 `rw` 进行等式替换
2. 用 `rw [Real.norm_eq_abs] at this` 而不是 `rw [← Real.norm_eq_abs]`
3. `linarith` 需要显式传递假设: `linarith [h1, h2, h3, h4]`

**当前状态**: 所有子引理已证明，但组合步骤中 `linarith` 的 `⊢ False` 问题尚未完全解决。

**建议**: 
- 尝试用 `omega` 或 `nlinarith` 代替 `linarith`
- 尝试用 `calc` 分步证明而不是 `have` + `linarith`
- 尝试在 `filter_upwards` 外部证明所有引理，然后在内部只用 `exact`
