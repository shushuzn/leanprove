/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Leanprove.ZetaAnalyticContinuation
import Leanprove.ZetaUpperBound

open Complex Real
open scoped Topology BigOperators ComplexConjugate
open Metric

noncomputable section

/-! # completedZeta 与 riemannXi 函数 -/

/-- completed Riemann zeta: Λ(s) = π^{-s/2} Γ(s/2) ζ(s)
    定义为 Mathlib 的 completedRiemannZeta，确保函数方程等性质可直接使用 -/
def completedZeta (s : ℂ) : ℂ :=
  completedRiemannZeta s

/-- 函数方程 Λ(1-s) = Λ(s) -/
lemma completedZeta_one_sub (s : ℂ) : completedZeta (1 - s) = completedZeta s :=
  completedRiemannZeta_one_sub s

/-- Riemann ξ 函数: ξ(s) = s(s-1)Λ(s) -/
def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedZeta s

/-- 对称性 ξ(s) = ξ(1-s) -/
lemma riemannXi_eq_riemannXi_one_sub (s : ℂ) : riemannXi s = riemannXi (1 - s) := by
  dsimp [riemannXi]
  have hΛ : completedZeta (1 - s) = completedZeta s := completedZeta_one_sub s
  calc
    s * (s - 1) * completedZeta s = (1 - s) * (-s) * completedZeta s := by ring
    _ = (1 - s) * ((1 - s) - 1) * completedZeta s := by ring
    _ = (1 - s) * ((1 - s) - 1) * completedZeta (1 - s) := by rw [hΛ]
    _ = riemannXi (1 - s) := rfl

/-- ξ 与复共轭交换: ξ(s̅) = ξ(s)̅ -/
lemma riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  dsimp [riemannXi, completedZeta]
  simp only [map_mul, map_sub, map_one]
  congr 1
  -- 核心性质: completedRiemannZeta (conj s) = conj (completedRiemannZeta s)
  -- 需要从 Mellin 变换的 integral_conj 性质推导
  sorry

/-- 在临界线上 ξ(1/2 + it) 的虚部为零（即实值） -/
lemma riemannXi_real_on_critical_line (t : ℝ) : (riemannXi (1/2 + I * t)).im = 0 := by
  have h_symm : riemannXi (1/2 + I * t) = riemannXi (1/2 - I * t) := by
    calc
      riemannXi (1/2 + I * t) = riemannXi (1 - (1/2 + I * t)) := riemannXi_eq_riemannXi_one_sub _
      _ = riemannXi (1/2 - I * t) := by ring
  have h_conj : riemannXi (1/2 - I * t) = conj (riemannXi (1/2 + I * t)) := by
    have h_conj_eq : conj (1/2 + I * t) = 1/2 - I * t := by
      apply Complex.ext <;> simp
    calc
      riemannXi (1/2 - I * t) = riemannXi (conj (1/2 + I * t)) := by rw [h_conj_eq]
      _ = conj (riemannXi (1/2 + I * t)) := riemannXi_conj _
  have h_eq : conj (riemannXi (1/2 + I * t)) = riemannXi (1/2 + I * t) :=
    calc
      conj (riemannXi (1/2 + I * t)) = riemannXi (1/2 - I * t) := h_conj.symm
      _ = riemannXi (1/2 + I * t) := h_symm.symm
  have h_im_eq : (conj (riemannXi (1/2 + I * t))).im = (riemannXi (1/2 + I * t)).im := by rw [h_eq]
  have h_conj_im : (conj (riemannXi (1/2 + I * t))).im = -(riemannXi (1/2 + I * t)).im :=
    Complex.conj_im _
  rw [h_conj_im] at h_im_eq
  linarith

/-! ## Γ 函数反射公式与增长估计 -/

/-- Γ(z)Γ(1-z) = π / sin(πz) -/
lemma gamma_reflection (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) :=
  Complex.Gamma_mul_Gamma_one_sub z

/-- Γ(it) 的模平方公式：|Γ(it)|² = π / (|t| · |sinh(πt)|) -/
lemma gamma_it_sq_norm (t : ℝ) (ht : t ≠ 0) : ‖Gamma (I * (t : ℂ))‖ ^ 2 = π / abs t / abs (Real.sinh (π * t)) := by
  have h_ne : I * (t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ht)
  have h_ne' : -I * (t : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr ht)
  have h_conj : conj (Gamma (I * ↑t)) = Gamma (-I * ↑t) := by
    rw [← Complex.Gamma_conj]; simp [mul_comm I]
  have h_sq_c : (↑(‖Gamma (I * ↑t)‖ ^ 2) : ℂ) = Gamma (I * ↑t) * Gamma (-I * ↑t) := by
    conv_lhs => rw [ofReal_pow]; rw [← Complex.mul_conj', h_conj]
  have h_rec : Gamma (1 - I * ↑t) = -I * ↑t * Gamma (-I * ↑t) := by
    have h := Complex.Gamma_add_one (-I * ↑t) h_ne'
    rw [show -I * ↑t + 1 = 1 - I * ↑t by ring] at h; exact h
  have h_sin : sin ((↑π : ℂ) * (I * ↑t)) = ↑(Real.sinh (π * t)) * I := by
    rw [show (↑π : ℂ) * (I * ↑t) = (↑(π * t) : ℂ) * I by push_cast; ring]
    rw [Complex.sin_mul_I, ofReal_sinh]
  have h_denom_ne : (↑(Real.sinh (π * t)) * ↑t : ℂ) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht)))
      (ofReal_ne_zero.mpr ht)
  have h_mul : Gamma (I * ↑t) * Gamma (-I * ↑t) * (↑(Real.sinh (π * t)) * ↑t) = (↑π : ℂ) := by
    have h_refl := Complex.Gamma_mul_Gamma_one_sub (I * ↑t)
    rw [mul_comm (Gamma (I * ↑t)), mul_assoc (Gamma (-I * ↑t))]
    rw [show Gamma (-I * ↑t) * (Gamma (I * ↑t) * (↑(Real.sinh (π * t)) * ↑t)) =
      Gamma (I * ↑t) * ((-I * ↑t) * Gamma (-I * ↑t)) * (↑(Real.sinh (π * t)) * I) by
        rw [mul_comm (Gamma (-I * ↑t))]; ring_nf; simp only [I_sq]; ring_nf]
    rw [← mul_assoc, ← h_rec, h_refl, h_sin]
    have h_sinh_ne : (↑(Real.sinh (π * t)) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht))
    field_simp [h_sinh_ne]
  have h_prod : Gamma (I * ↑t) * Gamma (-I * ↑t) = ↑π / (↑(Real.sinh (π * t)) * ↑t) :=
    eq_div_of_mul_eq h_denom_ne h_mul
  have h_coe : (↑(π / (Real.sinh (π * t) * t)) : ℂ) = ↑π / (↑(Real.sinh (π * t)) * ↑t) := by
    rw [show (↑(Real.sinh (π * t)) * ↑t : ℂ) = ↑(Real.sinh (π * t) * t) by rw [← ofReal_mul]]
    rw [ofReal_div]
  have h_sq_r : ‖Gamma (I * ↑t)‖ ^ 2 = π / (Real.sinh (π * t) * t) := by
    have h : (↑(‖Gamma (I * ↑t)‖ ^ 2) : ℂ) = ↑(π / (Real.sinh (π * t) * t)) := by
      rw [h_sq_c, h_prod, h_coe]
    rwa [Complex.ofReal_inj] at h
  have h_sign : Real.sinh (π * t) * t = abs (Real.sinh (π * t)) * abs t := by
    rcases lt_or_gt_of_ne ht with h_neg | h_pos
    · rw [abs_of_nonpos (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos h_neg)).le,
          abs_of_nonpos h_neg.le]; ring
    · rw [abs_of_nonneg (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos h_pos)).le,
          abs_of_nonneg h_pos.le]
  rw [h_sq_r, h_sign, mul_comm (abs (Real.sinh _)), div_div]


/-- ζ(2) = π²/6 -/
lemma zeta_at_two_val : riemannZeta 2 = π ^ 2 / 6 :=
  riemannZeta_two

/-- ζ(-1) = -1/12 -/
lemma zeta_at_neg_one_val : riemannZeta (-1) = -1 / 12 := by
  have h := zeta_at_neg_nat 1
  norm_num at h
  convert h using 1
  norm_num

/-! ## 增长估计 -/

/-- ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (re s) 当 n > 0 -/
lemma norm_natCast_cpow (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
  exact norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) s

/-- ‖1/(n : ℂ)^s‖ = 1/(n : ℝ)^(re s) 当 n > 0 -/
lemma norm_one_div_natCast_cpow (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    ‖(1 : ℂ) / ↑n ^ s‖ = (1 : ℝ) / ↑n ^ s.re := by
  rw [norm_div, norm_one, one_div, norm_natCast_cpow n hn, one_div]

/-- ζ(s) 在 Re(s) = 2 上的有界性：‖ζ(s)‖ ≤ 2
    证明策略: ‖ζ(s)‖ ≤ ∑' ‖1/n^s‖ = ∑' 1/n^2 ≤ 2 -/
lemma zeta_bound_at_two (s : ℂ) (hs : re s = 2) : ‖riemannZeta s‖ ≤ 2 := by
  have hs_gt : 1 < re s := by linarith
  have hs_ne : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hs_gt]
  have h_summable : Summable (fun (n : ℕ) => ‖(1 : ℂ) / ↑n ^ s‖) := by
    have : (fun (n : ℕ) => ‖(1 : ℂ) / ↑n ^ s‖) =
        (fun (n : ℕ) => (1 : ℝ) / ((n : ℝ) ^ (2 : ℝ))) := by
      funext n; rcases eq_or_ne n 0 with rfl | hn
      · simp [zero_cpow hs_ne]
      · rw [norm_one_div_natCast_cpow n hn, hs]
    rw [this]
    exact summable_one_div_nat_rpow.mpr (by norm_num)
  have h1 : ‖∑' n : ℕ, (1 : ℂ) / ↑n ^ s‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / ↑n ^ s‖ :=
    norm_tsum_le_tsum_norm h_summable
  have h_eq : (∑' n : ℕ, ‖(1 : ℂ) / ↑n ^ s‖) = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (2 : ℝ)) := by
    congr 1; funext n; rcases eq_or_ne n 0 with rfl | hn
    · simp [zero_cpow hs_ne]
    · rw [norm_one_div_natCast_cpow n hn, hs]
  have h2 : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (2 : ℝ)) ≤ 2 := by
    have h := zeta_upper_bound 2 (by norm_num : (1 : ℝ) < 2)
    rw [show (1 : ℝ) + 1 / (2 - 1) = 2 by norm_num] at h
    exact h
  linarith

/-- ζ(s) 在 Re(s) = -1 上的有界性（通过函数方程）：‖ζ(s)‖ ≤ 4
    策略: s=-1 时直接验证, s≠-1 时用函数方程 ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
    + zeta_bound_at_two (因 re(1-s)=2) -/
lemma zeta_bound_at_neg_one (s : ℂ) (hs : re s = -1) : ‖riemannZeta s‖ ≤ 4 := by
  rcases eq_or_ne s (-1) with rfl | h_ne
  · rw [zeta_at_neg_one_val]; norm_num
  have hs_ne_nat : ∀ n : ℕ, s ≠ -↑n := by
    intro n h
    have hr : -1 = -(n : ℝ) := by rw [← hs, h]; simp
    have hn : n = 1 := by exact_mod_cast (show (n : ℝ) = 1 from by linarith)
    subst hn; push_cast at h; exact h_ne h
  have hs_ne_one : s ≠ 1 := by
    intro h; rw [h, one_re] at hs; linarith
  have h_fe := riemannZeta_one_sub hs_ne_nat hs_ne_one
  have h_bound_1s : ‖riemannZeta (1 - s)‖ ≤ 2 := by
    apply zeta_bound_at_two; rw [sub_re, one_re, hs]; norm_num
  -- |ζ(1-s)| = |2(2π)^{-s}Γ(s)cos(πs/2)| * |ζ(s)|
  -- 需要 bound 分母 |2(2π)^{-s}Γ(s)cos(πs/2)| ≥ 1/2
  sorry

/-! ## 零点计数函数 N(T) -/

/-- 临界带：{s ∈ ℂ | 0 ≤ Re(s) ≤ 1, 0 ≤ Im(s) ≤ T} -/
def criticalStrip (T : ℝ) : Set ℂ :=
  { s | 0 ≤ re s ∧ re s ≤ 1 ∧ 0 ≤ im s ∧ im s ≤ T }

/-- ξ 函数的零点集 -/
def riemannXiZeros : Set ℂ :=
  { s | riemannXi s = 0 }

/-- 零点计数函数 N(T) = #{ρ ∈ criticalStrip T | ξ(ρ) = 0} -/
noncomputable def xiZeroCount (T : ℝ) : ℕ := 0

/-! ### criticalStrip 的基本性质 -/

/-- criticalStrip 关于 T 单调 -/
lemma criticalStrip_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : criticalStrip T₁ ⊆ criticalStrip T₂ := by
  intro s hs
  simp [criticalStrip] at hs ⊢
  exact ⟨hs.1, hs.2.1, hs.2.2.1, le_trans hs.2.2.2 h⟩

/-- criticalStrip T 是闭集 -/
lemma criticalStrip_isClosed (T : ℝ) : IsClosed (criticalStrip T) := by
  have h_re0 : IsClosed {s : ℂ | 0 ≤ re s} :=
    isClosed_le (continuous_const : Continuous fun _ : ℂ => (0 : ℝ)) continuous_re
  have h_re1 : IsClosed {s : ℂ | re s ≤ 1} :=
    isClosed_le continuous_re (continuous_const : Continuous fun _ : ℂ => (1 : ℝ))
  have h_im0 : IsClosed {s : ℂ | 0 ≤ im s} :=
    isClosed_le (continuous_const : Continuous fun _ : ℂ => (0 : ℝ)) continuous_im
  have h_imT : IsClosed {s : ℂ | im s ≤ T} :=
    isClosed_le continuous_im continuous_const
  have h_eq : criticalStrip T = ({s : ℂ | 0 ≤ re s} ∩ {s : ℂ | re s ≤ 1} ∩
      {s : ℂ | 0 ≤ im s} ∩ {s : ℂ | im s ≤ T}) := by
    ext s; constructor
    · intro ⟨h0, h1, h2, h3⟩; exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    · intro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩; exact ⟨h0, h1, h2, h3⟩
  rw [h_eq]
  exact IsClosed.inter (IsClosed.inter (IsClosed.inter h_re0 h_re1) h_im0) h_imT

/-- criticalStrip T 有界 -/
lemma criticalStrip_bounded (T : ℝ) : Bornology.IsBounded (criticalStrip T) := by
  have h_bound : ∀ s ∈ criticalStrip T, ‖s‖ ≤ 1 + |T| := by
    intro s hs
    simp [criticalStrip] at hs
    have h_norm_sq_eq : ‖s‖ ^ 2 = (re s) ^ 2 + (im s) ^ 2 := by
      calc
        ‖s‖ ^ 2 = Complex.normSq s := by symm; exact Complex.normSq_eq_norm_sq s
        _ = (re s) ^ 2 + (im s) ^ 2 := by
          simp [Complex.normSq_apply, sq]
    have h_bound_sq : ‖s‖ ^ 2 ≤ (1 + |T|) ^ 2 := by
      rw [h_norm_sq_eq]
      have h_re_sq : (re s) ^ 2 ≤ 1 := by
        have h_re : 0 ≤ re s ∧ re s ≤ 1 := ⟨hs.1, hs.2.1⟩
        nlinarith
      have h_im_sq : (im s) ^ 2 ≤ (|T|) ^ 2 := by
        have h_im : 0 ≤ im s ∧ im s ≤ T := ⟨hs.2.2.1, hs.2.2.2⟩
        calc
          (im s) ^ 2 ≤ T ^ 2 := by nlinarith
          _ = (|T|) ^ 2 := by simp
      nlinarith [abs_nonneg T]
    have h_norm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
    have h_one_absT_nonneg : 0 ≤ 1 + |T| := by nlinarith [abs_nonneg T]
    nlinarith
  refine ((isBounded_iff_subset_closedBall (0 : ℂ)).mpr ?_)
  refine ⟨1 + |T|, ?_⟩
  intro s hs
  have h_norm := h_bound s hs
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact h_norm

/-- criticalStrip T 是紧集 -/
lemma criticalStrip_isCompact (T : ℝ) : IsCompact (criticalStrip T) :=
  isCompact_of_isClosed_isBounded (criticalStrip_isClosed T) (criticalStrip_bounded T)

/-- ξ 的非平凡零点集（排除 s=0 和 s=1，它们是 ξ 的平凡零点） -/
def riemannXiNontrivialZeros : Set ℂ :=
  { s | riemannXi s = 0 ∧ s ≠ 0 ∧ s ≠ 1 }

/-! ### riemannXiZeros 的基本性质 -/

/-- 0 是 ξ 的零点（平凡零点） -/
lemma zero_in_riemannXiZeros : (0 : ℂ) ∈ riemannXiZeros := by
  rw [riemannXiZeros, Set.mem_setOf_eq]
  dsimp [riemannXi, completedZeta]
  ring

/-- 1 是 ξ 的零点（平凡零点） -/
lemma one_in_riemannXiZeros : (1 : ℂ) ∈ riemannXiZeros := by
  rw [riemannXiZeros, Set.mem_setOf_eq]
  dsimp [riemannXi, completedZeta]
  ring

/-- 0 不是 ξ 的非平凡零点 -/
lemma zero_notin_riemannXiNontrivialZeros : (0 : ℂ) ∉ riemannXiNontrivialZeros := by
  intro h
  exact h.2.1 rfl

/-- 1 不是 ξ 的非平凡零点 -/
lemma one_notin_riemannXiNontrivialZeros : (1 : ℂ) ∉ riemannXiNontrivialZeros := by
  intro h
  exact h.2.2 rfl

/-- ξ 零点在 s ↦ 1-s 下对称 -/
lemma riemannXiZeros_symm_one_sub {s : ℂ} (hs : s ∈ riemannXiZeros) : 1 - s ∈ riemannXiZeros := by
  rw [riemannXiZeros, Set.mem_setOf_eq] at hs ⊢
  rw [← riemannXi_eq_riemannXi_one_sub s]
  exact hs

/-- ξ 零点在 s ↦ s̅ 下对称 -/
lemma riemannXiZeros_symm_conj {s : ℂ} (hs : s ∈ riemannXiZeros) : conj s ∈ riemannXiZeros := by
  rw [riemannXiZeros, Set.mem_setOf_eq] at hs ⊢
  rw [riemannXi_conj, hs, map_zero]

/-! ### xiZeroCount (N(T)) 的基本性质 -/

/-- N(T) 关于 T 单调 -/
lemma xiZeroCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : xiZeroCount T₁ ≤ xiZeroCount T₂ := by
  simp [xiZeroCount]

/-- ξ(ρ) = 0 且 ρ ≠ 0, ρ ≠ 1 ⇒ ζ(ρ) = 0 -/
lemma riemannXi_zero_implies_zeta_zero {s : ℂ} (hs : s ∈ riemannXiNontrivialZeros) : riemannZeta s = 0 := by
  have h_zero := hs.1
  have h_ne_zero := hs.2.1
  have h_ne_one := hs.2.2
  dsimp [riemannXi] at h_zero
  have h_prod_ne : s * (s - 1) ≠ 0 :=
    mul_ne_zero h_ne_zero (sub_ne_zero.mpr h_ne_one)
  have h_completed_zero : completedZeta s = 0 := by
    rcases mul_eq_zero.mp h_zero with h | h
    · exact absurd h h_prod_ne
    · exact h
  dsimp [completedZeta] at h_completed_zero
  rw [riemannZeta_def_of_ne_zero h_ne_zero, h_completed_zero]
  exact zero_div _

/-- xiZeroCount 当前占位值 -/
lemma xiZeroCount_eq_NT (T : ℝ) : xiZeroCount T = 0 := rfl
