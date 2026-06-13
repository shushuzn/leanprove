# Sorry 清单和进展

## 当前状态 (2026-06-14)

**总 sorry 数: 31**

## 已证明

1. ✅ `fourierIntegral_self_add_deriv_deriv` - (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` - CS函数Fourier变换连续
3. ✅ `decay_bounds_key` - Fourier衰减估计 (完整证明)
4. ✅ `decay_bounds_cor` - CS函数衰减估计 (完整证明)

## 待证明

### 高优先级
- `decay_bounds_W21` (line 344) - W21函数衰减估计
  - 子任务已细化，待组合到主文件

### 中优先级
- `W21_integrable_fourier` (line 347) - W21函数Fourier变换可积
- `W21_integrable_fourier_restrict` (line 351) - W21函数Fourier变换限制可积

### 低优先级
- 其他 sorry 在 WienerProof.lean 后半部分

## 证明策略

### decay_bounds_W21
```
‖𝓕(f) u‖ ≤ w21norm * (1+u²)⁻¹  (decay_bounds_key)
w21norm = ∫‖f‖ + 1/(4π²) * ∫‖f''‖
∫‖f‖ ≤ π*A  (decay_bounds_aux + hA)
1/(4π²) * ∫‖f''‖ ≤ A/(4π)  (decay_bounds_aux + hA' + 代数)
w21norm ≤ π*A + A/(4π) = (π + 1/(4π))*A
‖𝓕(f) u‖ ≤ (π + 1/(4π))*A * (1+u²)⁻¹ = (π + 1/(4π))*A/(1+u²)
```
