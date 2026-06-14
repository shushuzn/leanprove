/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- Phase IV-D: Euler Product for the Riemann Zeta Function
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Leanprove.ZetaIVB

open Complex Filter Nat
open scoped Topology BigOperators

/-!
### Phase IV-D: Euler 乘积公式

ζ(s) = ∏_p (1 - p^{-s})⁻¹ 对 Re(s) > 1

基于 mathlib 的 `riemannZeta_eulerProduct` 系列定理。
-/

/-! #### 基本性质 -/

/-- ζ(σ) 的实部为正 (σ > 1) -/
theorem riemannZeta_real_pos (σ : ℝ) (hσ : 1 < σ) :
    0 < (riemannZeta (σ : ℂ)).re :=
  riemannZeta_re_pos_of_one_lt hσ

/-- ζ(σ) ≠ 0 对 σ > 1 (因为实部 > 0) -/
theorem riemannZeta_ne_zero_real (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)

/-! #### Euler 乘积 — 复数形式 (直接包装 mathlib 定理) -/

/-- Euler 乘积 (HasProd): ∏_p (1 - p^{-s})⁻¹ 收敛到 ζ(s), Re(s) > 1 -/
abbrev euler_product_hasProd := @riemannZeta_eulerProduct_hasProd

/-- Euler 乘积 (tprod): ∏' p : Primes, (1 - p^{-s})⁻¹ = ζ(s), Re(s) > 1 -/
abbrev euler_product_tprod := @riemannZeta_eulerProduct_tprod

/-- Euler 乘积 (有限乘积极限): ∏_{p<n} (1 - p^{-s})⁻¹ → ζ(s), Re(s) > 1 -/
abbrev euler_product_tendsto := @riemannZeta_eulerProduct

/-! #### 实数 → 复数 Euler 因子桥梁 -/

/-- ofReal (1 - p^{-σ}) = 1 - cpow (↑p) (ofReal (-σ)) : 实因子嵌入 ℂ -/
private lemma ofReal_euler_factor_base (p : ℕ) (hp : p.Prime) (σ : ℝ) :
    ofReal ((1 : ℝ) - (p : ℝ) ^ (-σ)) =
    1 - cpow (p : ℂ) (ofReal (-σ)) := by
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := (Nat.cast_pos.mpr hp.pos).le
  have h_coe : ((p : ℝ) : ℂ) = (p : ℂ) := by norm_cast
  rw [ofReal_sub, ofReal_one]
  rw [ofReal_cpow hp_nonneg, h_coe, cpow_eq_pow]

/-! #### Euler 乘积 — 实数特化 -/

/-- Euler 乘积实数形式 (有限乘积极限):
    ∏_{p<n, p prime} (1 - p^{-σ})⁻¹ → ζ(σ), σ > 1 -/
theorem euler_product_real_tendsto (σ : ℝ) (hσ : 1 < σ) :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n,
      (ofReal ((1 : ℝ) - (p : ℝ) ^ (-σ)))⁻¹)
      atTop (𝓝 (riemannZeta (σ : ℂ))) := by
  have h_main := riemannZeta_eulerProduct (s := (σ : ℂ)) (by simp [hσ])
  -- Step 1: Replace real base with cpow form using ofReal
  have h_eq₁ : (fun n : ℕ => ∏ p ∈ primesBelow n,
      (ofReal ((1 : ℝ) - (p : ℝ) ^ (-σ)))⁻¹) =
    (fun n : ℕ => ∏ p ∈ primesBelow n,
      (1 - cpow ((p : ℕ) : ℂ) (ofReal (-σ)))⁻¹) := by
    ext n
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp_prime : p.Prime := prime_of_mem_primesBelow hp
    rw [ofReal_euler_factor_base p hp_prime σ]
  -- Step 2: cpow = ^ and ofReal(-σ) = -(σ : ℂ)
  have h_eq₂ : (fun n : ℕ => ∏ p ∈ primesBelow n,
      (1 - cpow ((p : ℕ) : ℂ) (ofReal (-σ)))⁻¹) =
    (fun n : ℕ => ∏ p ∈ primesBelow n,
      (1 - ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) := by
    ext n
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [cpow_eq_pow]
    congr 1
    simp [ofReal_neg]
  rw [h_eq₁, h_eq₂]
  exact h_main

/-- Euler 乘积实数形式 (HasProd):
    ∏_p (1 - p^{-σ})⁻¹ (作为复数) 收敛到 ζ(σ), σ > 1 -/
theorem euler_product_real_hasProd (σ : ℝ) (hσ : 1 < σ) :
    HasProd (fun p : Primes =>
      (ofReal ((1 : ℝ) - ((p : ℕ) : ℝ) ^ (-σ)))⁻¹)
      (riemannZeta (σ : ℂ)) := by
  have h_main := riemannZeta_eulerProduct_hasProd (s := (σ : ℂ)) (by simp [hσ])
  convert h_main using 1
  ext p
  have hp_prime : (p : ℕ).Prime := p.2
  -- Use ofReal_euler_factor_base to convert, then cpow_eq_pow and ofReal_neg
  rw [ofReal_euler_factor_base (p : ℕ) hp_prime σ, cpow_eq_pow]
  congr 1
  simp [ofReal_neg]
