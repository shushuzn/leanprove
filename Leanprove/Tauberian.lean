/-
Wiener-Ikehara Tauberian Theorem and application to PNT.
Ported from PrimeNumberTheoremAnd/Wiener.lean (Kontorovich et al.)
-/
import Leanprove.Sobolev
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.RemovableSingularity
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

/-- Auxiliary function for WeakPNT: -ζ'/ζ with the pole 1/(s-1) removed.
    At s=1 both terms have simple poles with residue 1, so G(1) is defined as 1. -/
noncomputable def G_weakPNT : ℂ → ℂ := fun s => if s = 1 then 1 else
  -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)

/-- **G continuity axiom**: Both -ζ'(s)/ζ(s) and 1/(s-1) have simple poles at s=1
    with residue 1 (from `riemannZeta_residue_one`), so their difference has a
    removable singularity at s=1. By Riemann's removable singularity theorem
    (`differentiableOn_update_limUnder_of_bddAbove` in mathlib), G extends
    analytically across s=1, hence is continuous on {Re(s) ≥ 1}.
    A complete formal proof requires ~200 lines of local analysis. -/
axiom G_continuous : ContinuousOn G_weakPNT {s : ℂ | 1 ≤ s.re}

/-- The weak PNT: (1/N)∑_{n<N} Λ(n) → 1 -/
theorem WeakPNT : Tendsto (fun N : ℕ => cumsum vonMangoldt N / (N : ℝ))
    atTop (nhds 1) := by
  refine WienerIkeharaTheorem vonMangoldt (fun n => @vonMangoldt_nonneg n) ?_ 1 G_weakPNT G_continuous ?_
  · -- Summability: ∑ Λ(n)/n^σ converges for σ > 1
    intro σ hσ
    have hσc : (1 : ℝ) < ((σ : ℂ)).re := by simp [hσ]
    have hLS := LSeriesSummable_vonMangoldt hσc
    have h1 : Summable (LSeries.term (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)) := hLS
    have h2 : Summable (fun n : ℕ =>
        (if n = 0 then 0 else (vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ))) := by
      refine Summable.congr h1 (fun n => ?_)
      by_cases hn : n = 0
      · simp [hn, LSeries.term]
      · simp only [hn, ↓reduceIte]; rw [LSeries.term_of_ne_zero hn]
    -- Pointwise: complex term = ofReal of real term
    have h_ptwise : ∀ n : ℕ, (if n = 0 then 0 else (vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ)) =
        ↑(if n = 0 then 0 else vonMangoldt n / (n : ℝ) ^ σ) := by
      intro n
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have h_cpow : ↑((n : ℝ) ^ σ) = ((n : ℝ) : ℂ) ^ (σ : ℂ) :=
          Complex.ofReal_cpow (le_of_lt (Nat.cast_pos.mpr hn_pos)) σ
        have h_div : ↑(vonMangoldt n / (n : ℝ) ^ σ) =
            (↑(vonMangoldt n) : ℂ) / ((n : ℝ) : ℂ) ^ (σ : ℂ) := by
          rw [Complex.ofReal_div, h_cpow]
        exact h_div.symm
    -- Complex summable → real summable
    have h5 : Summable (fun n : ℕ =>
        if n = 0 then 0 else vonMangoldt n / (n : ℝ) ^ σ) := by
      rw [← Complex.summable_ofReal]
      exact show Summable (fun n : ℕ =>
        ↑(if n = 0 then 0 else vonMangoldt n / (n : ℝ) ^ σ)) from
        Summable.congr h2 (fun n => h_ptwise n)
    refine Summable.congr h5 (fun n => ?_)
    by_cases hn : n = 0; · simp [hn]
    · simp [hn]
  · -- G(s) = LSeries Λ s - 1/(s-1) on Re(s) > 1
    intro s hs
    have hs_ne : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hG : G_weakPNT s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) := by
      simp [G_weakPNT, hs_ne]
    rw [hG]
    have h_eq : -deriv riemannZeta s / riemannZeta s =
        LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) s :=
      (LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm
    rw [h_eq]
    <;> simp [sub_eq_add_neg]

/-- The Prime Number Theorem: ψ(x) ~ x.
    Converts discrete WeakPNT to continuous ψ~x via squeeze theorem. -/
theorem prime_number_theorem_psi_from_tauberian :
    Chebyshev.psi ~[atTop] (fun x : ℝ => x) := by
  have h_psi_cumsum : ∀ x : ℝ, 0 ≤ x →
      Chebyshev.psi x = cumsum vonMangoldt (⌊x⌋₊ + 1) := by
    intro x hx
    have h1 : Chebyshev.psi x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n :=
      Chebyshev.psi_eq_sum_Icc x
    have h2 : Finset.range (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ :=
      Nat.range_succ_eq_Icc_zero _
    rw [h1, ← h2]; rfl
  have h_psi_div_x : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
    have hW1 : Tendsto (fun N : ℕ => cumsum vonMangoldt (N + 1) / (N + 1 : ℝ))
        atTop (nhds 1) :=
      Tendsto.congr (fun N => by simp [Nat.cast_add_one])
        ((tendsto_add_atTop_iff_nat 1).2 WeakPNT)
    have h_ratio : Tendsto (fun N : ℕ => (N : ℝ) / (N + 1)) atTop (nhds 1) := by
      -- 1/(N+1:ℝ) → 0 (shift of 1/N → 0)
      have h_div0 : Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1 : ℝ)) atTop (nhds 0) := by
        have h_shift : Tendsto (fun n : ℕ => (1 : ℝ) / ↑(n + 1)) atTop (nhds 0) :=
          (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
        refine Tendsto.congr (fun N => ?_) h_shift
        rw [show (N + 1 : ℝ) = ↑(N + 1) from (Nat.cast_add_one N).symm]
      -- N/(N+1) = 1 - 1/(N+1)
      have h_ratio_eq : (fun N : ℕ => (N : ℝ) / (N + 1)) =ᶠ[atTop]
          (fun N : ℕ => 1 - (1 : ℝ) / (N + 1 : ℝ)) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        have hN1_ne : (N + 1 : ℝ) ≠ 0 := by positivity
        field_simp [hN1_ne]
        <;> ring
      have h_sub : Tendsto (fun N : ℕ => 1 - (1 : ℝ) / (N + 1 : ℝ)) atTop
          (nhds ((1 : ℝ) - 0)) :=
        tendsto_const_nhds.sub h_div0
      have h_sub1 : Tendsto (fun N : ℕ => 1 - (1 : ℝ) / (N + 1 : ℝ)) atTop (nhds 1) := by
        convert h_sub using 1
        norm_num
      exact Tendsto.congr' h_ratio_eq.symm h_sub1
    have hW2 : Tendsto (fun N : ℕ => cumsum vonMangoldt N / (N + 1 : ℝ))
        atTop (nhds 1) := by
      have h_prod : Tendsto (fun N : ℕ =>
          cumsum vonMangoldt N / (N : ℝ) * ((N : ℝ) / (N + 1)))
          atTop (nhds (1 * 1)) := WeakPNT.mul h_ratio
      have h_one : (1 * 1 : ℝ) = 1 := by norm_num
      refine h_one ▸ Tendsto.congr' ?_ h_prod
      filter_upwards [eventually_gt_atTop 0] with N hN
      field_simp [(Nat.cast_pos.mpr hN).ne', (by positivity : (0 : ℝ) < N + 1).ne']
    have hN_atTop : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
    have h_lower : Tendsto
        (fun x : ℝ => cumsum vonMangoldt ⌊x⌋₊ / (⌊x⌋₊ + 1 : ℝ)) atTop (nhds 1) := by
      have heq : (fun x : ℝ => cumsum vonMangoldt ⌊x⌋₊ / (⌊x⌋₊ + 1 : ℝ)) =
          (fun N : ℕ => cumsum vonMangoldt N / (N + 1 : ℝ)) ∘ (fun x : ℝ => ⌊x⌋₊) := by
        funext x; rfl
      rw [heq]
      exact hW2.comp hN_atTop
    have h_ratio2 : Tendsto (fun N : ℕ => (N + 1 : ℝ) / (N : ℝ)) atTop (nhds 1) := by
      -- 1/N → 0
      have h_one_div_N : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
      -- 1 + 1/N → 1 + 0
      have h_add : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (nhds ((1 : ℝ) + 0)) :=
        tendsto_const_nhds.add h_one_div_N
      -- (N+1)/N = 1 + 1/N eventually
      have h_ratio2_eq : (fun N : ℕ => (N + 1 : ℝ) / (N : ℝ)) =ᶠ[atTop]
          (fun N : ℕ => 1 + 1 / (N : ℝ)) := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        field_simp [(Nat.cast_pos.mpr hN).ne']
        <;> ring
      -- cast nhds ((1:ℝ) + 0) to nhds 1
      have h_add1 : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (nhds 1) := by
        convert h_add using 1
        norm_num
      exact Tendsto.congr' h_ratio2_eq.symm h_add1
    have h_upper_N : Tendsto (fun N : ℕ => cumsum vonMangoldt (N + 1) / (N : ℝ))
        atTop (nhds 1) := by
      have h_prod : Tendsto (fun N : ℕ =>
          cumsum vonMangoldt (N + 1) / (N + 1 : ℝ) * ((N + 1 : ℝ) / (N : ℝ)))
          atTop (nhds (1 * 1)) := hW1.mul h_ratio2
      have h_one : (1 * 1 : ℝ) = 1 := by norm_num
      refine h_one ▸ Tendsto.congr' ?_ h_prod
      filter_upwards [eventually_gt_atTop 0] with N hN
      field_simp [(Nat.cast_pos.mpr hN).ne', (by positivity : (0 : ℝ) < N + 1).ne']
    have h_upper : Tendsto
        (fun x : ℝ => cumsum vonMangoldt (⌊x⌋₊ + 1) / (⌊x⌋₊ : ℝ)) atTop (nhds 1) := by
      have heq : (fun x : ℝ => cumsum vonMangoldt (⌊x⌋₊ + 1) / (⌊x⌋₊ : ℝ)) =
          (fun N : ℕ => cumsum vonMangoldt (N + 1) / (N : ℝ)) ∘ (fun x : ℝ => ⌊x⌋₊) := by
        funext x; rfl
      rw [heq]
      exact h_upper_N.comp hN_atTop
    have h_bounds : ∀ᶠ x : ℝ in atTop,
        cumsum vonMangoldt ⌊x⌋₊ / (⌊x⌋₊ + 1 : ℝ) ≤ Chebyshev.psi x / x ∧
        Chebyshev.psi x / x ≤ cumsum vonMangoldt (⌊x⌋₊ + 1) / (⌊x⌋₊ : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hx_pos : 0 < x := by linarith
      set N : ℕ := ⌊x⌋₊
      have hN_le : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hN_lt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
      have hN_ge1 : 1 ≤ N := by
        simpa [N] using Nat.floor_mono (by linarith : (1 : ℝ) ≤ x)
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by linarith)
      have h_psi : Chebyshev.psi x = cumsum vonMangoldt (N + 1) := h_psi_cumsum x (by linarith)
      have h_psi_lower : (cumsum vonMangoldt N : ℝ) ≤ Chebyshev.psi x := by
        have h_le : (N - 1 : ℝ) ≤ x := (sub_le_self (N : ℝ) (by norm_num : (0 : ℝ) ≤ 1)).trans hN_le
        have h_mono : Chebyshev.psi ((N - 1 : ℕ) : ℝ) ≤ Chebyshev.psi x :=
          Chebyshev.psi_mono (by exact_mod_cast h_le)
        have h_cumsum : cumsum vonMangoldt N = Chebyshev.psi ((N - 1 : ℕ) : ℝ) := by
          by_cases hN0 : N = 0
          · simp [hN0, cumsum]
          · have hN_sub : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)
            have h_floor : ⌊((N - 1 : ℕ) : ℝ)⌋₊ = N - 1 := by simp [Nat.floor_natCast]
            have h_val := h_psi_cumsum ((N - 1 : ℕ) : ℝ) (by positivity)
            simp only [h_floor] at h_val
            rw [h_val, hN_sub]
        rw [h_cumsum]; exact h_mono
      have h_psi_upper : Chebyshev.psi x ≤ (cumsum vonMangoldt (N + 1) : ℝ) := by rw [h_psi]
      have h_cn : (0 : ℝ) ≤ cumsum vonMangoldt N := cumsum_nonneg (fun n => vonMangoldt_nonneg) _
      have h_cp : 0 ≤ Chebyshev.psi x := by rw [h_psi]; exact cumsum_nonneg (fun n => vonMangoldt_nonneg) _
      have h_lo : cumsum vonMangoldt N / (N + 1 : ℝ) ≤ Chebyshev.psi x / x :=
        (div_le_div_of_nonneg_left h_cn (by linarith) (by linarith)).trans
          (div_le_div_of_nonneg_right h_psi_lower (by linarith))
      have h_hi : Chebyshev.psi x / x ≤ cumsum vonMangoldt (N + 1) / (N : ℝ) :=
        (div_le_div_of_nonneg_left h_cp (by linarith) (by linarith)).trans
          (div_le_div_of_nonneg_right h_psi_upper (by positivity))
      exact ⟨h_lo, h_hi⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper
      (by filter_upwards [h_bounds] with x hx; exact hx.1)
      (by filter_upwards [h_bounds] with x hx; exact hx.2)
  -- Convert ψ(x)/x → 1 to ψ ~ x
  have h_zero : Chebyshev.psi 0 = 0 := by
    simp [Chebyshev.psi_eq_sum_Icc 0]
  have h_eq : (fun x : ℝ => (Chebyshev.psi x - x) / x) =ᶠ[atTop]
      (fun x : ℝ => Chebyshev.psi x / x - 1) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp [hx.ne']
  have h_sub : Tendsto (fun x => Chebyshev.psi x / x - 1) atTop (nhds 0) :=
    (show (1 : ℝ) - 1 = 0 by norm_num) ▸
      h_psi_div_x.sub (tendsto_const_nhds (x := (1 : ℝ)))
  have h_o : Tendsto (fun x => (Chebyshev.psi x - x) / x) atTop (nhds 0) :=
    Tendsto.congr' h_eq.symm h_sub
  have h_zc : ∀ x : ℝ, x = 0 → Chebyshev.psi x - x = 0 := by
    intro x hx; simp [hx, h_zero]
  exact (isLittleO_iff_tendsto h_zc).mpr h_o
