/-
Copyright (c) 2024 Alex Kontorovich, et al.
Ported from PrimeNumberTheoremAnd/Sobolev.lean

Sobolev-type function spaces for Wiener-Ikehara Tauberian theorem.
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Complex.RealDeriv

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap BigOperators
open scoped ContDiff

set_option maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- C^n functions with compact support -/
@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

namespace CS

variable {f : CS n E} {x : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

/-- Coerce a real-valued CS function to a complex-valued one -/
instance coeRealComplex : Coe (CS n ℝ) (CS n ℂ) where
  coe f := ⟨fun x => ↑(f x),
    ofRealCLM.contDiff.comp f.h1,
    f.h2.comp_left (g := Complex.ofReal) rfl⟩

instance : Add (CS n E) where add f g :=
  ⟨f.toFun + g.toFun, f.h1.add g.h1, f.h2.add g.h2⟩

@[simp] lemma add_apply {f g : CS n E} {x : ℝ} : (f + g) x = f x + g x := rfl

end CS

/-- Sobolev W^{n,1}: functions with integrable derivatives up to order n -/
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

/-- W^{2,1}(ℝ, ℂ) — the key Sobolev space for Wiener-Ikehara -/
abbrev W21 := W1 2 ℂ

namespace W1

variable {f : W1 n E}

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

/-- Negation in W1 -/
def neg (f : W1 n E) : W1 n E where
  toFun := -f
  smooth := f.smooth.neg
  integrable := fun k hk => by
    have eq : iteratedDeriv k (-f.toFun) = -(iteratedDeriv k f.toFun) := by
      funext x; exact iteratedDeriv_neg k f.toFun x
    rw [eq]
    exact (f.integrable hk).neg

instance : Neg (W1 n E) where neg := neg

@[simp] lemma neg_apply {f : W1 n E} {x : ℝ} : (-f) x = -(f x) := rfl

/-- Addition in W1 -/
instance : Add (W1 n E) where add f g :=
  ⟨f.toFun + g.toFun, f.smooth.add g.smooth,
   fun k hk => by
    have eq : iteratedDeriv k (f.toFun + g.toFun) =
        iteratedDeriv k f.toFun + iteratedDeriv k g.toFun := by
      funext x
      have hf : ContDiffAt ℝ k f.toFun x := (f.smooth.of_le (mod_cast hk)).contDiffAt
      have hg : ContDiffAt ℝ k g.toFun x := (g.smooth.of_le (mod_cast hk)).contDiffAt
      exact iteratedDeriv_add hf hg
    rw [eq]
    exact (f.integrable hk).add (g.integrable hk)⟩

@[simp] lemma add_apply {f g : W1 n E} {x : ℝ} : (f + g) x = f x + g x := rfl

end W1

/-- The W^{2,1} norm: ‖f‖_{W^{2,1}} = ∫ |f| + ∫ |f'| + ∫ |f''| -/
noncomputable def W21norm (f : W21) : ℝ :=
  (∫ x : ℝ, ‖f x‖) + (∫ x : ℝ, ‖iteratedDeriv 1 f x‖) + (∫ x : ℝ, ‖iteratedDeriv 2 f x‖)

lemma W21norm_nonneg (f : W21) : 0 ≤ W21norm f := by
  dsimp [W21norm]
  have h₁ : 0 ≤ ∫ (x : ℝ), ‖(f : ℝ → ℂ) x‖ :=
    integral_nonneg (fun x => @norm_nonneg ℂ _ _)
  have h₂ : 0 ≤ ∫ (x : ℝ), ‖iteratedDeriv 1 (f : ℝ → ℂ) x‖ :=
    integral_nonneg (fun x => @norm_nonneg ℂ _ _)
  have h₃ : 0 ≤ ∫ (x : ℝ), ‖iteratedDeriv 2 (f : ℝ → ℂ) x‖ :=
    integral_nonneg (fun x => @norm_nonneg ℂ _ _)
  exact add_nonneg (add_nonneg h₁ h₂) h₃

/-- Truncation function: a C² bump function with specific bounds.
    ≥ 1 on [-1,1], ≤ 0 outside (-2,2), ≤ 1 everywhere. -/
structure TruncFun where
  toCS : CS 2 ℝ
  ge_one : ∀ x, x ∈ Set.Icc (-1) 1 → (1 : ℝ) ≤ toCS x
  nonpos_outside : ∀ x, x ∉ Set.Ioo (-2) 2 → toCS x ≤ 0
  le_one : ∀ x, toCS x ≤ 1

instance truncFun_coeFun : CoeFun TruncFun (fun _ => ℝ → ℝ) where
  coe t := t.toCS.toFun
