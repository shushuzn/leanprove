/-
Phase VI: Riemann Xi function and Hardy's theorem.
ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Polynomial
import Leanprove.ZetaIVE

open Complex Real
open scoped Topology BigOperators

noncomputable section

/-- completed Riemann zeta: Λ(s) = π^{-s/2}Γ(s/2)ζ(s) -/
def completedZeta (s : ℂ) : ℂ :=
  (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s

lemma completedZeta_one_sub (s : ℂ) : completedZeta (1 - s) = completedZeta s :=
  completedRiemannZeta_one_sub s

/-- Riemann ξ 函数: ξ(s) = s(s-1)Λ(s) -/
def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedZeta s

lemma riemannXi_eq_riemannXi_one_sub (s : ℂ) : riemannXi s = riemannXi (1 - s) := by
  dsimp [riemannXi]
  have hΛ : completedZeta (1 - s) = completedZeta s := completedZeta_one_sub s
  calc
    s * (s - 1) * completedZeta s = (1 - s) * (-s) * completedZeta s := by ring
    _ = (1 - s) * ((1 - s) - 1) * completedZeta (1 - s) := by
      simp [hΛ]
      ring
    _ = riemannXi (1 - s) := rfl

/-- ξ 函数与复共轭交换: ξ(s̅) = ξ(s)̅ -/
lemma riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  dsimp [riemannXi, completedZeta]
  simp [map_mul, map_add, map_sub, conj_pow, conj_neg, conj_ofReal, Gamma_conj, riemannZeta_conj]

/-- 在临界线上 ξ(1/2 + it) 是实值函数 -/
lemma riemannXi_real_on_critical_line (t : ℝ) : riemannXi (1/2 + I * t) ∈ ℝ := by
  have h_symm : riemannXi (1/2 + I * t) = riemannXi (1/2 - I * t) := by
    calc
      riemannXi (1/2 + I * t) = riemannXi (1 - (1/2 + I * t)) := riemannXi_eq_riemannXi_one_sub _
      _ = riemannXi (1/2 - I * t) := by ring
  have h_conj : riemannXi (1/2 - I * t) = conj (riemannXi (1/2 + I * t)) := by
    calc
      riemannXi (1/2 - I * t) = riemannXi (conj (1/2 + I * t)) := by simp
      _ = conj (riemannXi (1/2 + I * t)) := riemannXi_conj _
  rw [h_symm, h_conj]
  exact conj_eq_self.mp rfl

/-- ξ 是整函数（利用 Λ₀ 的整函数性）-/
lemma riemannXi_isEntire : Differentiable ℂ riemannXi := by
  have h_formula : ∀ s : ℂ, riemannXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := by
    intro s
    dsimp [riemannXi, completedZeta]
    have hΛ_eq : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
      completedRiemannZeta_eq s
    rw [hΛ_eq]
    ring
  refine (Differentiable.mul ?_ ?_).add (differentiable_const 1)
  · exact differentiable_id.mul (differentiable_id.sub differentiable_const)
  · exact differentiable_completedZeta₀

/-! #### 增长估计 -/

/-- ζ(s) 在 Re(s) = 2 上绝对收敛：|ζ(2 + it)| ≤ ζ(2) -/
lemma zeta_bound_at_two (t : ℝ) : ‖riemannZeta (2 + I * t)‖ ≤ riemannZeta (2 : ℂ) := by
  have hs : 1 < (2 + I * t).re := by
    simp
    norm_num
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hsum : Summable (fun n : ℕ => ‖1 / ((n : ℂ) ^ (2 + I * t))‖) := by
    have h_abs_eq : ∀ n : ℕ, n ≠ 0 → ‖1 / ((n : ℂ) ^ (2 + I * t))‖ = 1 / ((n : ℝ) ^ (2 : ℝ)) := by
      intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos (2 + I * t), norm_natCast,
        norm_ofReal]
    refine .of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (by
      refine (summable_nat_add_iff 1).mpr ?_
      have : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℝ))) := by
        simpa using Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < (2 : ℝ))
      convert this
      ext n
      simp)
    by_cases hn0 : n = 0
    · subst hn0; simp
    · rw [h_abs_eq n hn0]
      exact le_rfl
  calc
    ‖∑' n : ℕ, 1 / ((n : ℂ) ^ (2 + I * t))‖ ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) ^ (2 + I * t))‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (2 : ℝ)) := by
      refine tsum_congr (fun n => ?_)
      by_cases hn0 : n = 0
      · subst hn0; simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        simp [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos (2 + I * t), norm_natCast,
          norm_ofReal]
    _ = riemannZeta (2 : ℂ) := by
      have h2 : 1 < (2 : ℂ).re := by norm_num
      rw [zeta_eq_tsum_one_div_nat_cpow h2]
      simp [div_eq_inv_mul]
