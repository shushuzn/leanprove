# Sorry 清单和进展

## 当前状态 (2026-06-14)

**总 sorry 数: 27**（从 29 减少）

## 已证明 (本次session)

1. ✅ `fourierIntegral_self_add_deriv_deriv` - (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` - CS函数Fourier变换连续
3. ✅ `decay_bounds_key` - 含三角不等式
4. ✅ `decay_bounds_cor` - CS函数嵌入W21
5. ✅ `decay_bounds_W21` - 含代数恒等式
6. ✅ `W21_integrable_fourier` - 含变量替换
7. ✅ `nnabla_mul_log_sq` - BigO渐近分析（本次新增）
8. ✅ `nnabla_bound_aux` - nnabla序列差分的BigO bound（本次新增）

## 关键经验

### nnabla_bound_aux 证明要点
- **策略**: 使用 IsBigO.of_bound 1 + filter_upwards + 简化
- **关键**: 展开 nnabla 定义，然后用 norm_eq_abs 简化绝对值
- **简化**: 对于递减函数，|nnabla u n| ≤ u n
- **bound**: 证明 u n ≤ 1/(log²n * n²) 通过比较分母
- **类型转换**: 使用 `exact_mod_cast` 处理 `n : ℕ` → `(n : ℝ)`
- **绝对值处理**: `rw [abs_of_nonneg (sub_nonneg.mpr h_decr)]` 可能失败，需要其他方法

### nnabla_mul_log_sq 证明要点
- **策略**: 展开 + bound + nlinarith
- **核心 bound**: `(x-1) * 2/(x-1) * (2|log x| + 2|log b|) = 4|log x| + 4|log b|`
- **关键转化**: `4|log x| + 4|log b| ≤ (4|log b| + 4) * log²x` 当 `log x ≥ 1` (即 x ≥ 3)
- **eventually_gt_atTop 3** 代替 2 (因为 2 < e < 3, log 2 < 1)
- **Real.exp_one_lt_three** 需要 `import Mathlib.Analysis.Complex.ExponentialBounds`
- **linarith 无法处理 Real.log**，但 nlinarith 配合 `sq_nonneg` 和 `1 ≤ log x` 可以
- **abs_of_pos 内部用 Real.log_pos 需要显式 `(by linarith : 1 < x)`**
- **div_pos (by linarith : 0 < x) hx1** 显式类型
- **不能向前引用 lemma**，需要把被引用的 lemma 放在前面

## 待证明 (27个)

按 skill 继续逐个证明