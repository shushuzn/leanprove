# 依赖链

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

- 无（全项目 0 axiom + 0 sorry）
- 所有证明完全依赖于 mathlib 内核

## 2026-06-12 类型修复记录

WienerProof.lean 中 `f : ℕ → ℝ` 与 `LSeries`/`cheby`/`nterm`（要求 `ℕ → ℂ`）的类型不匹配已修复：
- `LSeries f s` → `LSeries (fun n ↦ (f n : ℂ)) s`
- `cheby f` / `nterm f σ'` → `cheby (fun n ↦ (f n : ℂ))` / `nterm (fun n ↦ (f n : ℂ)) σ'`
- `chebyWith C f` → `chebyWith C (fun n ↦ (f n : ℂ))`
- 新增 `hnorm : ∀ i, ‖(f i : ℂ)‖ = f i` 桥接实数/复数范数
