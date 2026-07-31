# Sorry 清单和进展

## 当前状态 (2026-07-31 审计校正，实测 grep `\bsorry\b`)

**Definitions.lean sorry 数: 1**（仅 zeta_bound_at_neg_one；riemannXi_conj 与 zeta_bound_at_two 已证明）

| 文件 | sorry 数 | 状态 |
|------|----------|------|
| Leanprove/CriticalLine/Definitions.lean | 1 | 🔄 仅 zeta_bound_at_neg_one（L249，需 Γ Stirling 上界，Mathlib 缺失） |
| Leanprove/CriticalLine/Hardy.lean | 2 | 🔄 criticalLineZeroCount_le_xiZeroCount（L114）+ criticalLineZeros_isDiscrete（L222） |
| Leanprove/WienerIkehara.lean | 30 | 🔄 底层 Fourier/可积性辅助引理待证 |
| **合计** | **33** | PrimeNumberTheorem.lean 0（L492 为注释非 sorry） |

> ⚠️ 审计说明：本节计数于 2026-07-31 用 `grep \bsorry\b` 逐文件实测校正。此前版本（2026-06-26）声称 Definitions=3、WienerIkehara=28 已过时：riemannXi_conj、zeta_bound_at_two、xi_on_critical_line_continuous 均已证明完成。

### riemannXi_conj 证明进展（✅ 已全部完成，2026-07-31 核实）

**已证明的组件**:
- `cpow_conj_of_real_pos`: `0 < t → (t:ℂ)^conj s = conj((t:ℂ)^s)` ✅
- `mellin_conj`: `mellin f (conj s) = conj (mellin f s)` 当 `conj (f t) = f t` ✅
  - 关键: `setIntegral_congr_fun measurableSet_Ioi` + `integral_conj`
- `conj_ofReal_comp`: `conj ((ofReal ∘ g) t) = (ofReal ∘ g) t` ✅
- `completedRiemannZeta_conj` → `riemannXi_conj`（Definitions.lean L99）✅ 已落地主文件

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

## CriticalLine/Definitions.lean（1 个）

| 行号 | 引理/定理 | 目标简述 | 状态 |
|------|-----------|----------|------|
| 249 | `zeta_bound_at_neg_one` | Re(s)=-1 时 ‖ζ(s)‖ ≤ 4·(1+\|Im s\|)^{3/2} | 🔄 函数方程已接好，剩 \|Γ(2-it)\|·\|cosh(πt/2)\| ≤ C·(1+\|t\|)^{3/2}（Γ Stirling 上界，Mathlib 无现成引理，见 mathlib-api.md §16 缺失警告） |

**已证明（2026-07-31 核实）**: `riemannXi_conj`（L99）✅、`zeta_bound_at_two`（L204）✅（用 `norm_natCast_cpow` + `norm_tsum_le_tsum_norm` + `riemannZeta_two` + `pi_lt_d2`）。

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

## CriticalLine/Hardy.lean（2 个）

| 行号 | 引理/定理 | 目标简述 |
|------|-----------|----------|
| 114 | `criticalLineZeroCount_le_xiZeroCount` | N₀(T) ≤ N(T)，Nat.card→encard + criticalLine 单射（见 mathlib-api.md §15） |
| 222 | `criticalLineZeros_isDiscrete` | 临界线零点集离散，用 IsolatedZeros（见 mathlib-api.md §14） |

**已证明（2026-07-31 核实）**: `xi_on_critical_line_continuous`（L200）✅、`criticalLineZeros_isClosed`（L214）✅。

## WienerIkehara.lean（30 个）

| 行号 | 引理/定理 | 目标简述 |
|------|-----------|----------|
| 792, 793, 802 | `nnabla_bound_aux` 内部 | 3 处：nlinarith 剩余目标 + log_div 展开 |
| 831 | `summable_inv_mul_log_sq` | 1/(n(log n)²) 可和（用 summable_condensed_iff，见 mathlib-api.md §12） |
| 876 | `limiting_fourier_lim1_aux` | Fourier 极限辅助一的可和性 bound |
| 897 | `limiting_fourier_lim1` 内部 | dominated convergence 的点态 bound |
| 903 | `limiting_fourier_lim3` | G(σ'+tI) 积分的连续性极限（见 §13 控制收敛） |
| 913 | `limiting_fourier_lim2` | 指数衰减积分极限 |
| 964 | `hf_coe1` | LSeries 项的 ENNReal 可和性（见 integral-api.md ENNReal 桥接） |
| 970 | `second_fourier_integrable_aux1a` | 指数衰减函数在 Ici 上可积（见 integral-api.md 指数衰减） |
| 977 | `second_fourier_integrable_aux1` | 乘积测度上可积（见 integral-api.md integrable_prod_iff） |
| 1005 | `second_fourier` | 第二 Fourier 恒等式 |
| 1012 | `first_fourier` | 第一 Fourier 恒等式 |
| 1023 | `limit_of_lseries_zero` | LSeries 零点 ⇒ 极限为零 |
| 1034 | `limiting_fourier_aux` | Fourier 极限辅助等式 |
| 1038 | `fourier_surjection_on_schwartz` | Schwartz 空间 Fourier 满射性 |
| 1083 | `limiting_cor` | 极限推论主定理 |
| 1088 | `W21_norm_fourier_integral_le` | W21 Fourier 积分范数上界 |
| 1096 | `continuous_LSeries_aux` | LSeries 沿 vertical line 连续 |
| 1113 | `comp_exp_support0` | 支撑在 Ioi 0 的函数在 0 附近为零 |
| 1118 | `comp_exp_support` | Ψ(exp x) 的紧支集性 |
| 1192 | `wiener_ikehara_smooth` | Wiener-Ikehara 光滑主引理 |
| 1203 | `limiting_cor_schwartz` | 极限推论 Schwartz 版本 |
| 1211 | `smooth_urysohn_support_Ioo` | 光滑 Urysohn 型 bump 函数 |
| 1219 | `interval_approx_inf` | 区间近似取下界 |
| 1225 | `interval_approx_sup` | 区间近似取上界 |
| 1300, 1304, 1305 | `residue_nonneg` 内部 | 3 处：Sψ 极限 = A·∫ψ；∫ψ > 0；0 ≤ A 最终推导 |
| 1355 | `WienerIkeharaInterval` | Wiener-Ikehara 区间定理 |

> 行号于 2026-07-31 用 `grep -n \bsorry\b` 实测，共 30 处（含三处内职 3+3）。

## 推荐证明顺序（2026-07-31 校正，仅列待证项）

1. **WienerIkehara.lean 底层可积性/可和性引理优先**：`summable_inv_mul_log_sq`（§12 condensed）、`second_fourier_integrable_aux1a/aux1`（integral-api.md 指数衰减/乘积）、`hf_coe1`（ENNReal 桥接）—— 无依赖，先攻。
2. **Fourier 恒等式与极限**：`first_fourier`/`second_fourier` → `limiting_fourier_lim1/2/3`（§13 控制收敛）→ `limiting_fourier_aux`/`limiting_cor`。
3. **residue_nonneg / WienerIkeharaInterval** —— 依赖上述极限结果。
4. **Hardy.lean**：`criticalLineZeroCount_le_xiZeroCount`（§15 encard 单射）、`criticalLineZeros_isDiscrete`（§14 IsolatedZeros）。
5. **zeta_bound_at_neg_one**（Definitions.lean L249）—— 阻塞于 Γ Stirling 上界（Mathlib 缺失，需自证，优先级最低）。

> ✅ 已证明（无需再做）：`riemannXi_conj`、`riemannXiZeros_symm_conj`、`zeta_bound_at_two`、`xi_on_critical_line_continuous`、`criticalLineZeros_isClosed`。

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
