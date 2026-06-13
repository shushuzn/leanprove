# 困难 Proof 记录

## nnabla_mul_log_sq (line 503)

**类型**: BigO渐近分析证明

**目标**: `x*(a + log²(x/b)) - (x-1)*(a + log²((x-1)/b)) = O(log²x)`

**证明思路**:
1. 展开: `a + log²(x/b) + (x-1)*(log²(x/b) - log²((x-1)/b))`
2. `a + log²(x/b) = O(log²x)` ✅ (子任务7a,7b,7c完成)
3. `(x-1)*(log²(x/b) - log²((x-1)/b)) = O(log²x)` ❌ (最难)

**第3步需要**:
- `log(x/b) - log((x-1)/b) = O(1/x)` (用 nabla_log + comp_tendsto)
- `log(x/b) + log((x-1)/b) = O(log x)` (用 log_add_div_isBigO_log)
- `(x-1) * O(1/x) * O(log x) = O(log x) = O(log²x)` (IsBigO 组合)

**困难**:
- `IsBigO.comp_tendsto` 需要 `Tendsto f atTop atTop` 类型
- `atTop` vs `Filter.atTop` 类型不匹配
- 需要 `Tendsto (fun x => x - 1) atTop atTop`
- BigO乘法组合: `(f*g) =O h` from `f =O h'` and `g =O h''` 需要 `h' * h'' ≤ h`

**建议**: 需要更多Mathlib渐近分析API知识，或者用 `norm_num` + `nlinarith` 直接证明bound
