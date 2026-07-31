# 依赖链

## 格式规范

所有 .lean 文件遵循 STYLE.md（基于 mathlib4 标准），包含：
- 版权头 (`Copyright (c) 2026`)
- `/- ... -/` docstring 格式
- `snake_case` 定理/引理命名
- 导入顺序：mathlib → 项目内部

## WeakPNT → 顶层 axiom

```
WeakPNT (Tauberian.lean)
  └─ WienerIkeharaTheorem (Tauberian.lean)
       └─ WienerProof.WienerIkeharaTheorem' (WienerProof.lean)
            └─ WienerIkeharaInterval (WienerProof.lean)
                 ├─ interval_approx_sup (WienerProof.lean)
                 │    └─ smooth_urysohn_support_Ioo (WienerProof.lean)  ✅ Real.smoothTransition
                 ├─ interval_approx_inf (WienerProof.lean)
                 │    └─ smooth_urysohn_support_Ioo (WienerProof.lean)  ✅ Real.smoothTransition
                 ├─ residue_nonneg
                 │    └─ wiener_ikehara_smooth_real
                 │         └─ wiener_ikehara_smooth
                 │              ├─ fourier_surjection_on_schwartz
                 │              │    └─ fourierTransformCLE (mathlib)
                 │              └─ limiting_cor_schwartz
                 │                   └─ limiting_cor
                 │                        ├─ limiting_fourier
                 │                        │    ├─ limiting_fourier_lim1
                 │                        │    │    └─ decay_bounds_cor
                 │                        │    │         └─ decay_bounds_key
                 │                        │    │              └─ fourierIntegral_self_add_deriv_deriv
                 │                        │    ├─ limiting_fourier_lim2
                 │                        │    └─ limiting_fourier_lim3
                 │                        └─ limiting_cor_aux
                 │                             └─ Real.zero_at_infty_fourier (mathlib)
                 └─ WI_sum_le / WI_sum_Iab_le'
```

## 模块依赖

```
PNTVA.lean
  └─ Tauberian.lean
       ├─ WienerProof.lean
       │    ├─ Sobolev.lean
       │    └─ mathlib (FourierTransform, LSeries, ...)
       └─ VonMangoldt.lean
            └─ mathlib (Chebyshev, LSeries, ...)
ZetaVI.lean（阶段 VI 聚合导入模块）
  ├─ ZetaVI/Definitions.lean（基础定义：completedZeta, riemannXi, criticalStrip, N(T)）
  │   ├─ ZetaIVE.lean
  │   └─ mathlib (RiemannZeta, Gamma, Complex.Basic, Topology)
  ├─ ZetaVI/Hardy.lean（Hardy 定理框架：临界线零点、IVT、无限变号归约）
  │   ├─ ZetaVI/Definitions.lean
  │   └─ mathlib (ContinuousOn, IntermediateValue, Topology)
  └─ ZetaVI/Asymptotics.lean（渐近分析核心：Gamma 渐近、均值积分归约）
      ├─ ZetaVI/Hardy.lean
      └─ mathlib (Asymptotics, Sinh, IntervalIntegral)
```

## 顶层假设

- **主构建（`Leanprove.lean`）**：0 axiom + 0 sorry
- **阶段 VI 子模块（`CriticalLine.lean`）**：3 sorry（未在主构建导入，处于独立维护）
  - [`CriticalLine/Definitions.lean:249`](file:///d:/OpenClaw/leanprove/Leanprove/CriticalLine/Definitions.lean#L249) — `zeta_bound_at_neg_one`
  - [`CriticalLine/Hardy.lean:114`](file:///d:/OpenClaw/leanprove/Leanprove/CriticalLine/Hardy.lean#L114) — `criticalLineZeroCount_le_xiZeroCount`
  - [`CriticalLine/Hardy.lean:222`](file:///d:/OpenClaw/leanprove/Leanprove/CriticalLine/Hardy.lean#L222) — `criticalLineZeros_isDiscrete`
- **`WienerIkehara.lean`**：顶层 `WienerIkeharaTheorem'` 已闭合；模块内 ~30 个子引理含 sorry / TODO（不影响主定理链的类型检查）
- 全部主构建证明完全依赖于 mathlib 内核
