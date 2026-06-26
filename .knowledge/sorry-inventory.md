# Sorry 清单和进展

## 当前状态 (2026-06-26)

**Definitions.lean sorry 数: 3**（riemannXi_conj, zeta_bound_at_two, zeta_bound_at_neg_one）

| 文件 | sorry 数 | 状态 |
|------|----------|------|
| Leanprove/CriticalLine/Definitions.lean | 3 | 🔄 riemannXi_conj 证明路径已清晰，mellin_conj 需深入 measure theory |
| Leanprove/CriticalLine/Hardy.lean | 2 | 🔄 待证明 |
| Leanprove/WienerIkehara.lean | 28 | 🔄 构建错误待修复 |

### riemannXi_conj 证明进展

**已证明的组件**:
- `cpow_conj_of_real_pos`: `0 < t → (t:ℂ)^conj s = conj((t:ℂ)^s)` ✅
- `mellin_conj`: `mellin f (conj s) = conj (mellin f s)` 当 `conj (f t) = f t` ✅
  - 关键: `setIntegral_congr_fun measurableSet_Ioi` + `integral_conj`
- `conj_ofReal_comp`: `conj ((ofReal ∘ g) t) = (ofReal ∘ g) t` ✅

**待证明的组件**:
- `completedRiemannZeta_conj`: 需要将 `completedRiemannZeta` 展开为 `mellin` 形式，然后应用 `mellin_conj`
- 从 `completedRiemannZeta_conj` 推导 `riemannXi_conj` 已在测试文件中完成

**关键突破**: `mellin_conj` 的证明使用 `setIntegral_congr_fun` (Mathlib `MeasureTheory.Integral.Bochner.Set`) 在 `Ioi 0` 上逐点证明，然后用 `integral_conj` 处理共轭积分

## 已证明（2026-06-26 新增）

1. ✅ `zero_in_riemannXiZeros` — 0 是 ξ 的平凡零点
2. ✅ `one_in_riemannXiZeros` — 1 是 ξ 的平凡零点
3. ✅ `zero_notin_riemannXiNontrivialZeros` — 0 不是非平凡零点
4. ✅ `one_notin_riemannXiNontrivialZeros` — 1 不是非平凡零点
5. ✅ `riemannXi_zero_implies_zeta_zero` — ξ(ρ)=0 且 ρ≠0,1 ⇒ ζ(ρ)=0

## 已证明（历史记录）

1. ✅ `fourierIntegral_self_add_deriv_deriv` — (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` — CS 函数 Fourier 变换连续
3. ✅ `decay_bounds_key` — 含三角不等式
4. ✅ `decay_bounds_cor` — CS 函数嵌入 W21
5. ✅ `decay_bounds_W21` — 含代数恒等式
6. ✅ `W21_integrable_fourier` — 含变量替换
7. ✅ `nnabla_mul_log_sq` — BigO 渐近分析
8. ✅ `nnabla_bound_aux` — nnabla 序列差分的 BigO bound（部分完成，内部仍有一个 sorry 在 line 760）

## CriticalLine/Definitions.lean（3 个）

| 行号 | 引理/定理 | 目标简述 | 状态 |
|------|-----------|----------|------|
| 50 | `riemannXi_conj` | ξ 与复共轭交换 ξ(s̅) = ξ(s)̅ | 🔄 证明路径: cpow_conj ✅ → mellin_conj → completedRiemannZeta_conj → riemannXi_conj |
| 140 | `zeta_bound_at_two` | Re(s)=2 时 ‖ζ(s)‖ ≤ 2 | 🔄 需要 norm_cpow_eq_rpow_re_of_pos + norm_tsum_le_tsum_norm |
| 144 | `zeta_bound_at_neg_one` | Re(s)=-1 时 ‖ζ(s)‖ ≤ 4 | 🔄 依赖 zeta_bound_at_two |

### 已证明的新定理（2026-06-26）

| 引理/定理 | 说明 |
|-----------|------|
| `zero_in_riemannXiZeros` | 0 是 ξ 的平凡零点 |
| `one_in_riemannXiZeros` | 1 是 ξ 的平凡零点 |
| `zero_notin_riemannXiNontrivialZeros` | 0 不是非平凡零点 |
| `one_notin_riemannXiNontrivialZeros` | 1 不是非平凡零点 |
| `riemannXi_zero_implies_zeta_zero` | 非平凡零点 ⇒ ζ(ρ)=0 |
| `riemannXiZeros_symm_conj` | 零点共轭对称（依赖 riemannXi_conj） |
| `cpow_conj_of_real_pos`（测试文件） | 实数 t>0 时 (t:ℂ)^conj s = conj((t:ℂ)^s) |

## CriticalLine/Hardy.lean（3 个）

| 行号 | 引理/定理 | 目标简述 |
|------|-----------|----------|
| 110 | `criticalLineZeroCount_le_xiZeroCount` | N₀(T) ≤ N(T) |
| 195 | `xi_on_critical_line_continuous` | ξ 在临界线上实值限制的连续性 |
| 207 | `criticalLineZeros_isDiscrete` | 临界线零点集是离散的 |

## WienerIkehara.lean（28 个）

| 行号 | 引理/定理 | 目标简述 |
|------|-----------|----------|
| 760 | `nnabla_bound_aux` 内部 | 完成 `nlinarith [?]` 后的剩余目标 |
| 790 | `summable_inv_mul_log_sq` | 1/(n(log n)²) 可和 |
| 835 | `limiting_fourier_lim1_aux` | Fourier 极限辅助一的可和性 bound |
| 856 | `limiting_fourier_lim1` 内部 | dominated convergence 的点态 bound |
| 862 | `limiting_fourier_lim3` | G(σ'+tI) 积分的连续性极限 |
| 872 | `limiting_fourier_lim2` | 指数衰减积分极限 |
| 923 | `hf_coe1` | LSeries 项的 ENNReal 可和性 |
| 929 | `second_fourier_integrable_aux1a` | 指数衰减函数在 Ici 上的可积性 |
| 936 | `second_fourier_integrable_aux1` | 乘积测度上的可积性 |
| 964 | `second_fourier` | 第二 Fourier 恒等式 |
| 971 | `first_fourier` | 第一 Fourier 恒等式 |
| 982 | `limit_of_lseries_zero` | LSeries 零点 ⇒ 极限为零 |
| 993 | `limiting_fourier_aux` | Fourier 极限辅助等式 |
| 997 | `fourier_surjection_on_schwartz` | Schwartz 空间 Fourier 满射性 |
| 1042 | `limiting_cor` | 极限推论主定理 |
| 1047 | `W21_norm_fourier_integral_le` | W21 Fourier 积分范数上界 |
| 1055 | `continuous_LSeries_aux` | LSeries 沿 vertical line 连续 |
| 1072 | `comp_exp_support0` | 支撑在 Ioi 0 的函数在 0 附近为零 |
| 1077 | `comp_exp_support` | Ψ(exp x) 的紧支集性 |
| 1151 | `wiener_ikehara_smooth` | Wiener-Ikehara 光滑主引理 |
| 1162 | `limiting_cor_schwartz` | 极限推论 Schwartz 版本 |
| 1170 | `smooth_urysohn_support_Ioo` | 光滑 Urysohn 型 bump 函数 |
| 1178 | `interval_approx_inf` | 区间近似取下界 |
| 1184 | `interval_approx_sup` | 区间近似取上界 |
| 1259 | `residue_nonneg` 内部 (key) | S ψ 的极限等于 A·∫ψ |
| 1263 | `residue_nonneg` 内部 (l4) | ∫ψ > 0 |
| 1264 | `residue_nonneg` 内部 (exact) | 0 ≤ A 的最终推导 |
| 1314 | `WienerIkeharaInterval` | Wiener-Ikehara 区间定理 |

## 推荐证明顺序

1. **riemannXi_conj** — 证明路径已清晰：`cpow_conj_of_real_pos` ✅ → `mellin_conj`（组合 cpow_conj + integral_conj）→ `completedRiemannZeta_conj`（从 mellin_conj 推导）→ `riemannXi_conj`。
2. **riemannXiZeros_symm_conj** — ✅ 已证明（依赖 riemannXi_conj）。
3. **zeta_bound_at_two** — 需要 `norm_cpow_eq_rpow_re_of_pos` + `norm_tsum_le_tsum_norm` + `riemannZeta_two`。
4. **zeta_bound_at_neg_one** — 通过函数方程归约到 zeta_bound_at_two。
5. **CriticalLine/Hardy.lean** — 依赖 Definitions 中的结果。
6. **WienerIkehara.lean** — 底层辅助引理优先（`limiting_fourier_lim*`, `first_fourier`, `second_fourier` 等）。

## 关键 API 发现

### cpow_conj_of_real_pos（项目自定义）
**签名**: `0 < t → (t : ℂ) ^ conj s = conj ((t : ℂ) ^ s)`
**证明**: `arg_ofReal_of_nonneg ht.le` + `cpow_conj` + `conj_ofReal`
**用途**: Mellin 变换共轭性质的关键组件

### norm_cpow_eq_rpow_re_of_pos
**Import**: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
**签名**: `0 < x → ‖(x : ℂ) ^ y‖ = x ^ y.re`
**用途**: 证明 ‖n^s‖ = n^(Re s)，用于 zeta_bound_at_two

## 关键经验（见各 RAG 文件）

- BigO 渐近分析模式 → `bigo-api.md`
- nnabla 证明要点 → `nnabla-api.md`
- nnabla_bound_aux 子任务分解 → `nnabla_bound_aux-subtasks.md`
- 困难 proof 记录 → `difficult-proofs.md`
- 关键 Pitfalls → `proof-patterns.md`
- Mathlib API 用法索引 → `mathlib-api.md`（新增）
