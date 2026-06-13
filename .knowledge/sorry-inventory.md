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

- `nnabla_mul_log_sq` (line 503) - BigO渐近分析证明
  - 子任务已细化，但涉及太多渐近分析API细节
  - 核心困难: `atTop` vs `Filter.atTop` 类型不匹配
  - 需要: log(x/b) = O(log x), log(x/b)² = O(log x²), a = o(log x²)

## 下一个

- `nnabla_bound_aux` (line 525) - nnabla bound
- `nnabla_bound` (line 530) - nnabla bound
- 其他sorry在WienerProof.lean后半部分
