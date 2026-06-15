# Sorry 清单和进展

## 当前状态 (2026-06-15)

**总 sorry 数: 43**（分布在 3 个文件）

| 文件 | sorry 数 | 状态 |
|------|----------|------|
| Leanprove/CriticalLine/Definitions.lean | 12 | 🔄 待证明 |
| Leanprove/CriticalLine/Hardy.lean | 3 | 🔄 待证明 |
| Leanprove/WienerIkehara.lean | 28 | 🔄 部分修复（h_bound, h_log_eq, h_ident 已修复，rw[h_abs_eq] 仍 sorry） |

## 已证明（历史记录）

1. ✅ `fourierIntegral_self_add_deriv_deriv` — (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` — CS 函数 Fourier 变换连续
3. ✅ `decay_bounds_key` — 含三角不等式
4. ✅ `decay_bounds_cor` — CS 函数嵌入 W21
5. ✅ `decay_bounds_W21` — 含代数恒等式
6. ✅ `W21_integrable_fourier` — 含变量替换
7. ✅ `nnabla_mul_log_sq` — BigO 渐近分析
8. ✅ `nnabla_bound_aux` — nnabla 序列差分的 BigO bound（部分完成，内部仍有一个 sorry 在 line 760）

## CriticalLine/Definitions.lean（12 个）

| 行号 | 引理/定理 | 目标简述 |
|------|-----------|----------|
| 26 | `completedZeta_one_sub` | 函数方程 Λ(1-s) = Λ(s) |
| 45 | `riemannXi_conj` | ξ 与复共轭交换 ξ(s̅) = ξ(s)̅ |
| 73 | `gamma_reflection` | Γ(z)Γ(1-z) = π / sin(πz) |
| 77 | `gamma_it_sq_norm` | ‖Γ(it)‖² = π / (|t|·|sinh(πt)|) |
| 85 | `zeta_at_neg_one_val` | ζ(-1) = -1/12 |
| 91 | `zeta_bound_at_two` | Re(s)=2 时 ‖ζ(s)‖ ≤ 2 |
| 95 | `zeta_bound_at_neg_one` | Re(s)=-1 时 ‖ζ(s)‖ ≤ 4（经函数方程） |
| 175 | `zero_notin_riemannXiZeros` | 0 不是 ξ 的零点 |
| 179 | `one_notin_riemannXiZeros` | 1 不是 ξ 的零点 |
| 189 | `riemannXiZeros_symm_conj` | ξ 零点在共轭下对称 |
| 195 | `xiZeroCount_mono` | N(T) 关于 T 单调 |
| 199 | `riemannXi_zero_implies_zeta_zero` | ξ(ρ)=0 ⇒ ρ≠0, ρ≠1, ζ(ρ)=0 |

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

1. **WienerIkehara.lean 的辅助引理优先**：很多高层定理依赖底层辅助引理（`limiting_fourier_lim*`, `first_fourier`, `second_fourier` 等）。
2. **CriticalLine/Definitions.lean 基础引理**：如 `completedZeta_one_sub`, `gamma_reflection`, `zeta_at_neg_one_val` 等，这些是 Hardy 定理和零点计数的基础。
3. **Hardy.lean**：依赖 Definitions 中的结果。

## 关键经验（见各 RAG 文件）

- BigO 渐近分析模式 → `bigo-api.md`
- nnabla 证明要点 → `nnabla-api.md`
- nnabla_bound_aux 子任务分解 → `nnabla_bound_aux-subtasks.md`
- 困难 proof 记录 → `difficult-proofs.md`
- 关键 Pitfalls → `proof-patterns.md`
- Mathlib API 用法索引 → `mathlib-api.md`（新增）
