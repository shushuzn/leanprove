/-
Wiener-Ikehara Tauberian Theorem and application to PNT.
Ported from PrimeNumberTheoremAnd/Wiener.lean (Kontorovich et al.)
-/
import Leanprove.Sobolev
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open Real Complex MeasureTheory Filter Set LSeries Asymptotics
open ArithmeticFunction
open scoped Topology

set_option maxHeartbeats 400000

/-! #### Discrete Analysis -/

/-- Partial sums: ∑_{i<n} u(i) -/
def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

/-- Forward difference: u(n+1) - u(n) -/
def nabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u (n + 1) - u n

/-- Backward difference: u(n) - u(n+1) -/
def nnabla [Sub E] (u : ℕ → E) (n : ℕ) : E := u n - u (n + 1)

/-- Shift: u(n+1) -/
def shift (u : ℕ → E) (n : ℕ) : E := u (n + 1)

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) : ∀ n, 0 ≤ cumsum u n :=
  fun n => Finset.sum_nonneg (fun i _ => hu i)

/-- Chebyshev-type bound -/
def chebyWith (C : ℝ) (f : ℕ → ℝ) : Prop := ∀ n, cumsum f n ≤ C * n

def cheby (f : ℕ → ℝ) : Prop := ∃ C, chebyWith C f

/-- von Mangoldt satisfies Chebyshev bound: ∑_{n<N} Λ(n) ≤ C*N -/
theorem vonMangoldt_cheby : cheby vonMangoldt := by
  refine ⟨Real.log 4 + 4, fun n => ?_⟩
  have hle : (cumsum vonMangoldt n : ℝ) ≤ Chebyshev.psi (n : ℝ) := by
    have : cumsum vonMangoldt n = ∑ i ∈ Finset.range n, vonMangoldt i := rfl
    rw [this]
    have hsub : ∑ i ∈ Finset.range n, vonMangoldt i ≤
        ∑ i ∈ Finset.Icc 0 n, vonMangoldt i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => vonMangoldt_nonneg
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    simpa [Chebyshev.psi_eq_sum_Icc] using hsub
  have hpsi : Chebyshev.psi (n : ℝ) ≤ (Real.log 4 + 4) * (n : ℝ) :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  exact hle.trans hpsi

/-! #### Wiener-Ikehara Tauberian Theorem -/

/-- **Wiener-Ikehara Tauberian Theorem** (axiom-based, pending full proof). -/
axiom WienerIkeharaTheorem
    (f : ℕ → ℝ) (hf_pos : ∀ n, 0 ≤ f n)
    (hf_sum : ∀ (σ : ℝ), 1 < σ → Summable (fun n : ℕ => f n / (n : ℝ) ^ σ))
    (A : ℝ)
    (G : ℂ → ℂ)
    (hG_cont : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG_eq : ∀ s : ℂ, 1 < s.re →
      G s = LSeries (fun n : ℕ => (f n : ℂ)) s - (A : ℂ) / (s - 1)) :
    Tendsto (fun N : ℕ => cumsum f N / (N : ℝ)) atTop (nhds A)

/-! #### Application to PNT -/

/-- The weak PNT: (1/N)∑_{n<N} Λ(n) → 1 -/
theorem WeakPNT : Tendsto (fun N : ℕ => cumsum vonMangoldt N / (N : ℝ))
    atTop (nhds 1) := by
  let G : ℂ → ℂ := fun s => -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)
  refine WienerIkeharaTheorem vonMangoldt (fun n => @vonMangoldt_nonneg n) ?_ 1 G ?_ ?_
  · -- Summability for σ > 1
    sorry
  · -- G is continuous on Re(s) ≥ 1
    sorry
  · -- G(s) = -ζ'/ζ - 1/(s-1) on Re(s) > 1
    sorry

/-- The Prime Number Theorem: ψ(x) ~ x -/
theorem prime_number_theorem_psi_from_tauberian :
    Chebyshev.psi ~[atTop] (fun x : ℝ => x) := by
  -- From WeakPNT (discrete) to continuous ψ(x) ~ x
  sorry
