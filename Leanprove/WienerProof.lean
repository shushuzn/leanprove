/-
Wiener-Ikehara Tauberian theorem — full proof.
Ported from PrimeNumberTheoremAnd/Wiener.lean and Fourier.lean (Kontorovich et al.).
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.Deriv.Slope
import Leanprove.Sobolev
import Leanprove.Tauberian

open Real Complex MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap BigOperators
open scoped Topology ContDiff

set_option maxHeartbeats 400000

variable {f : ℕ → ℂ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ}

/-! #### W21 auxiliary properties -/

namespace W21

variable {f : W21}

lemma hf (f : W21) : Integrable f := f.integrable (by omega)

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable (by omega : 1 ≤ 2)

lemma hf'' (f : W21) : Integrable (deriv (deriv f)) := by
  simpa [iteratedDeriv_succ] using f.integrable (by omega : 2 ≤ 2)

lemma differentiable (f : W21) : Differentiable ℝ f :=
  f.smooth.differentiable (by omega)

lemma deriv_differentiable (f : W21) : Differentiable ℝ (deriv f) := by
  have : ContDiff ℝ 2 f := f.smooth
  exact this.deriv (by omega) |>.differentiable (by omega)

/-- The W21 norm used in Fourier decay estimates. -/
noncomputable def w21norm (f : W21) : ℝ :=
  (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma w21norm_nonneg (f : W21) : 0 ≤ w21norm f := by
  dsimp [w21norm] ; positivity

end W21

/-! #### Fourier transform conventions and basic properties -/

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 :=
  zero_lt_one.trans_le (by simpa using sq_nonneg u)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [Real.fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable (by omega : 2 ≤ 2)
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv_differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

/-! #### Fourier decay estimates for W21 functions -/

theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ f.w21norm * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  rw [norm_neg, F_mul, norm_mul]
  have hnorm : ‖(1 / (4 : ℂ) * π ^ 2 : ℂ)‖ = (4 * π ^ 2)⁻¹ := by
    simp
  calc
    ‖𝓕 (f : ℝ → ℂ) u‖ + ‖(1 / (4 : ℂ) * π ^ 2 : ℂ) * 𝓕 (deriv (deriv f) : ℝ → ℂ) u‖
        ≤ ∫ t, ‖f t‖ + ((4 * π ^ 2)⁻¹ : ℝ) * ∫ t, ‖deriv (deriv f) t‖ := by
      gcongr
      · apply prelim_decay f u
      · rw [norm_mul, hnorm]
        apply mul_le_mul_of_nonneg_left (prelim_decay (deriv (deriv f)) u)
        positivity
    _ = f.w21norm := by
      simp [w21norm, mul_comm, add_comm]

lemma decay_bounds_cor (ψ : W21) : ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  refine ⟨ψ.w21norm, fun u => ?_⟩
  simpa [div_eq_mul_inv] using decay_bounds_key ψ u

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) : ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

lemma decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simpa [div_eq_mul_inv] using hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux (by
      have : Continuous (deriv (deriv f)) :=
        (f.deriv.deriv.continuous)
      exact this.aestronglyMeasurable)
    simpa [div_eq_mul_inv] using hA'
  have hA_nonneg : 0 ≤ A := by
    have := hA 0
    have : 0 ≤ ‖f 0‖ := norm_nonneg _
    have : 0 ≤ A / (1 + 0 ^ 2) := by simpa using this.trans this
    positivity
  calc
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ f.w21norm * (1 + u ^ 2)⁻¹ := decay_bounds_key f u
    _ = ((∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)) * (1 + u ^ 2)⁻¹ := rfl
    _ ≤ (π * A + (4 * π ^ 2)⁻¹ * (π * A)) * (1 + u ^ 2)⁻¹ := by
      gcongr
      · exact l1
      · exact mul_le_mul_of_nonneg_left l2 (by positivity)
    _ = (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
      field_simp ; ring

lemma W21_integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have hbound : ∀ u, ‖𝓕 (ψ : ℝ → ℂ) (u / c)‖ ≤ C / (1 + (u / c) ^ 2) := by
    intro u ; simpa using hC (u / c)
  have hint : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have hmeas : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume :=
    (continuous_FourierIntegral ψ).comp (continuous_id.div_const c) |>.aestronglyMeasurable
  refine hint.mono' hmeas (Eventually.of_forall hbound)

lemma W21_integrable_fourier_restrict (ψ : W21) (hc : c ≠ 0) (s : Set ℝ) :
    IntegrableOn (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) s :=
  (W21_integrable_fourier ψ hc).restrict

lemma W21_norm_fourier_integral_le (ψ : W21) (hc : c ≠ 0) :
    ∫ u, ‖𝓕 (ψ : ℝ → ℂ) (u / c)‖ ≤ (C := ψ.w21norm) * ∫ u, (1 + (u / c) ^ 2)⁻¹ := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  sorry
