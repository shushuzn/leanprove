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
ZetaVI.lean (阶段 VI — ξ 对称性 + 临界线实值性)
  └─ ZetaIVE.lean
       └─ mathlib (RiemannZeta, Gamma, ...)
```

## 顶层假设

- 无（全项目 0 axiom + 0 sorry）
- 所有证明完全依赖于 mathlib 内核
