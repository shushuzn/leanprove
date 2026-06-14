# Sorry 清单和进展

## 当前状态 (2026-06-14)

**总 sorry 数: 29**

## 已证明 (本次session)

1. ✅ `fourierIntegral_self_add_deriv_deriv` - (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` - CS函数Fourier变换连续
3. ✅ `decay_bounds_key` - Fourier衰减估计 (完整证明)
4. ✅ `decay_bounds_cor` - CS函数衰减估计 (完整证明)
5. ✅ `decay_bounds_W21` - W21函数衰减估计 (完整证明)
6. ✅ `W21_integrable_fourier` - Fourier变换可积性 (完整证明)

## 当前攻克

### `nnabla_mul_log_sq` (line 503) - BigO渐近分析证明

**目标**: `x*(a + log²(x/b)) - (x-1)*(a + log²((x-1)/b)) = O(log²x)`

**子任务进展**:
- ✅ 7a: `log(x/b) = O(log x)` - 用 `log_add_div_isBigO_log 0 hb` + `simp only [add_zero]`
- ✅ 7b: `log(x/b)² = O(log x²)` - 用 `.sq`
- ✅ 7c: `a = o(log x²)` - 用 `isLittleO_const_of_tendsto_atTop`
- ✅ 7d1: `log(x/b) - log((x-1)/b) = log(x/(x-1))` - 用 `rw [Real.log_div ...]` + `ring_nf`
- ✅ 7d2: `|log(x/(x-1))| ≤ 2/(x-1)` - 用 `abs_of_pos` + `log_le_sub_one_of_pos` + `div_sub_one`
- ✅ 7d3: `|log(x/b) + log((x-1)/b)| ≤ 2|log x| + 2|log b|` - 用 `convert_to` + `norm_add_le` + `abs_sub`
- ❌ 7e: 组合步骤 - `linarith` 在 `filter_upwards` 上下文中看到 `⊢ False`

**核心困难**: 在 `filter_upwards` + `have` 上下文中，`linarith` 看到 `⊢ False` 而不是正确的目标。独立测试中所有子引理都成功。

**关键发现**:
1. `rw [← Real.norm_eq_abs]` 在 `have` 内部会影响主目标
2. `rw [Real.norm_eq_abs] at this` 是安全的
3. `convert_to` + `congr_arg₂` 可以代替 `rw` 进行等式替换
4. `linarith [h1, h2, h3, h4]` 需要显式传递假设

## 下一个

- `nnabla_bound_aux` (line 525) - nnabla bound
- `nnabla_bound` (line 530) - nnabla bound
- 其他sorry在WienerProof.lean后半部分
