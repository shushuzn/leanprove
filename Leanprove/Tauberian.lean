/-
Wiener-Ikehara Tauberian Theorem and application to PNT.
Ported from PrimeNumberTheoremAnd/Wiener.lean (Kontorovich et al.)
-/
import Leanprove.Sobolev
import Leanprove.WienerProof
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Slope

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
  fun _n => Finset.sum_nonneg (fun i _ => hu i)

/-- Chebyshev-type bound -/
def chebyWith (C : ℝ) (f : ℕ → ℝ) : Prop := ∀ n, cumsum f n ≤ C * n

def cheby (f : ℕ → ℝ) : Prop := ∃ C, chebyWith C f

/-- `nterm`: term of the Dirichlet series used for summability testing.
    For `f : ℕ → ℝ` and `0 ≤ f`, we have `nterm f σ n = f n / n ^ σ`. -/
def nterm (f : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else f n / (n : ℝ) ^ σ

/-- `term f s n` is the complex term of the Dirichlet series of `f` at `s`. -/
def term (f : ℕ → ℝ) (s : ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else (f n : ℂ) / n ^ s

/-- `term` agrees with `LSeries.term` applied to the complexified `f`. -/
lemma term_eq_LSeries_term (f : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    term f s n = LSeries.term (fun n => (f n : ℂ)) s n := by
  by_cases h : n = 0
  · simp [h, term, LSeries.term]
  · simp [h, term, LSeries.term, h.ne]

/-- The Dirichlet series of `f` equals the sum of `term f s n`. -/
theorem LSeries_eq_tsum_term (f : ℕ → ℝ) (s : ℂ) :
    LSeries (fun n => (f n : ℂ)) s = ∑' n, term f s n := by
  simp [LSeries, LSeries.term, term_eq_LSeries_term, tsum_congr fun n => ?_]

/-- `S f ε N`: weighted average over `[⌈ε * N⌉₊, N)`. -/
noncomputable def S (f : ℕ → ℝ) (ε : ℝ) (N : ℕ) : ℝ :=
  (∑ n in Finset.Ico ⌈ε * N⌉₊ N, f n) / N

/-- Auxiliary tendsto lemma for `S` function -/
lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

lemma S_sub_S {f : ℕ → ℝ} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) :
    S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using l2.trans_lt h1

/-- Wiener-Ikehara for an interval indicator -/
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (fun n => f n / (n : ℝ) ^ σ))
    (hcheby : cheby f) (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
    (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ => (∑' n, f n * indicator (Ioc a b) 1 (n / x)) / x) atTop (nhds (A * (b - a))) := by
  sorry

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (fun n => f n / (n : ℝ) ^ σ))
    (hcheby : cheby f) (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
    (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ => (∑ n in Finset.Ico a' b', f n) / N) atTop (nhds (A * (b - a))) := by
  sorry

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

/-- **Wiener-Ikehara Tauberian Theorem** (proved via WienerProof.lean). -/
theorem WienerIkeharaTheorem
    (f : ℕ → ℝ) (hf_pos : ∀ n, 0 ≤ f n)
    (hf_sum : ∀ (σ : ℝ), 1 < σ → Summable (fun n : ℕ => f n / (n : ℝ) ^ σ))
    (hcheby : cheby f)
    (A : ℝ)
    (G : ℂ → ℂ)
    (hG_cont : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG_eq : ∀ s : ℂ, 1 < s.re →
      G s = LSeries (fun n : ℕ => (f n : ℂ)) s - (A : ℂ) / (s - 1)) :
    Tendsto (fun N : ℕ => cumsum f N / (N : ℝ)) atTop (nhds A) := by
  -- Convert hypotheses to WienerProof format
  have hpos : 0 ≤ f := hf_pos
  have hf : ∀ (σ' : ℝ), 1 < σ' → Summable (WienerProof.nterm f σ') := by
    intro σ' hσ'
    have := hf_sum σ' hσ'
    refine Summable.congr (fun n => ?_) this
    by_cases hn : n = 0
    · simp [hn, WienerProof.nterm]
    · simp [WienerProof.nterm, hn, hf_pos n]
  have hcheby' : WienerProof.cheby f := by
    obtain ⟨C, hC⟩ := hcheby
    refine ⟨C, fun n => ?_⟩
    have : cumsum (‖f ·‖) n = cumsum f n := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp [hf_pos i]
    simpa [this] using hC n
  have hG' : Set.EqOn G (fun s ↦ LSeries (fun n : ℕ ↦ (f n : ℂ)) s - (A : ℂ) / (s - 1)) {s | 1 < s.re} :=
    hG_eq
  exact WienerProof.WienerIkeharaTheorem' hpos hf hcheby' hG_cont hG'

/-! #### Application to PNT -/

/-- Auxiliary function for WeakPNT: -ζ'/ζ with the pole 1/(s-1) removed.
    Both terms have simple poles at s=1 with residue 1; their difference
    has a removable singularity. The limit as s→1 is -γ (negative
    Euler-Mascheroni constant), computed via H(s) = (s-1)ζ(s):
    -ζ'/ζ - 1/(s-1) = -H'/H → -γ since H(1)=1 and H'(1)=γ. -/
noncomputable def G_weakPNT : ℂ → ℂ := fun s => if s = 1 then
  -(Real.eulerMascheroniConstant : ℂ) else
  -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)

/-- **G continuity**: G_weakPNT is continuous on {Re(s) ≥ 1}.
    The poles of -ζ'/ζ and 1/(s-1) at s=1 cancel, leaving a removable singularity
    with limit -γ (proven via H(s) = (s-1)ζ(s)). -/
theorem G_continuous : ContinuousOn G_weakPNT {s : ℂ | 1 ≤ s.re} := by
  let H_set : Set ℂ := {s | 1 ≤ s.re}
  let f_ext : ℂ → ℂ := fun s ↦ -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)
  have hG_eq : G_weakPNT = Function.update f_ext 1 (-(Real.eulerMascheroniConstant : ℂ)) := by
    funext s; by_cases hs : s = 1 <;> simp [G_weakPNT, f_ext, hs, Function.update]
  rw [hG_eq]
  -- Define h(s) = (s-1)·ζ(s) with continuous extension h(1) = 1
  let h : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  have h_one_val : h 1 = 1 := by simp [h]
  have h_one_ne_zero : h 1 ≠ 0 := by simp [h]
  have h_cont_one : ContinuousAt h 1 := by
    simpa [h, continuousAt_update_same] using riemannZeta_residue_one
  have h_diff_punct : ∀ᶠ s in 𝓝[≠] 1, DifferentiableAt ℂ h s := by
    have h_underlying_diff : ∀ᶠ s in 𝓝[≠] 1,
        DifferentiableAt ℂ (fun s ↦ (s - 1) * riemannZeta s) s := by
      filter_upwards [self_mem_nhdsWithin (a := (1 : ℂ)) (s := {1}ᶜ)] with (s : ℂ) hs
      exact ((differentiableAt_id (𝕜 := ℂ)).sub (differentiableAt_const (𝕜 := ℂ) (1 : ℂ))).mul
        (differentiableAt_riemannZeta hs)
    have h_eq : h =ᶠ[𝓝[≠] 1] (fun s ↦ (s - 1) * riemannZeta s) := by
      filter_upwards [self_mem_nhdsWithin (a := (1 : ℂ)) (s := {1}ᶜ)] with (s : ℂ) hs
      simp [h, Function.update_of_ne hs]
    have h_self_mem : ∀ᶠ (s : ℂ) in 𝓝[≠] 1, s ≠ 1 := by
      have h : {1}ᶜ ∈ 𝓝[≠] (1 : ℂ) := by
        rw [show 𝓝[≠] (1 : ℂ) = 𝓝[{1}ᶜ] (1 : ℂ) by rfl]
        exact self_mem_nhdsWithin
      filter_upwards [h] with s hs
      simpa using hs
    filter_upwards [h_underlying_diff, h_eq, h_self_mem] with s hs_diff h_eq_val hs_ne
    have h_eq_near : h =ᶠ[𝓝 s] (fun s ↦ (s - 1) * riemannZeta s) := by
      have h_open : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
      have h_mem : s ∈ ({1}ᶜ : Set ℂ) := hs_ne
      filter_upwards [h_open.mem_nhds h_mem] with x hx
      simp [h, Function.update_of_ne hx]
    exact hs_diff.congr_of_eventuallyEq h_eq_near
  have h_analytic_one : AnalyticAt ℂ h 1 :=
    analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt h_diff_punct h_cont_one
  have h_hasDerivAt_one : HasDerivAt h (Real.eulerMascheroniConstant : ℂ) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h_slope_eq : (fun s ↦ slope h 1 s) =ᶠ[𝓝[≠] 1]
        (fun s ↦ riemannZeta s - 1 / (s - 1)) := by
      filter_upwards [self_mem_nhdsWithin (a := (1 : ℂ)) (s := {1}ᶜ)] with (s : ℂ) hs
      have hs_ne : s ≠ 1 := hs
      calc
        slope h 1 s = (h s - h 1) / (s - 1) := by rw [slope_def_field]
        _ = (((s - 1) * riemannZeta s) - 1) / (s - 1) := by
          simp [h, Function.update_of_ne hs_ne]
        _ = riemannZeta s - 1 / (s - 1) := by
          have h : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne
          field_simp [h]
    exact Tendsto.congr' h_slope_eq.symm tendsto_riemannZeta_sub_one_div
  have h_deriv_one : deriv h 1 = (Real.eulerMascheroniConstant : ℂ) :=
    h_hasDerivAt_one.deriv
  have h_g_analytic_one : AnalyticAt ℂ (fun s ↦ -deriv h s / h s) 1 := by
    have h_deriv_analytic_one : AnalyticAt ℂ (deriv h) 1 := h_analytic_one.deriv
    exact (AnalyticAt.neg h_deriv_analytic_one).div h_analytic_one h_one_ne_zero
  have h_g_cont_one : ContinuousAt (fun s ↦ -deriv h s / h s) 1 :=
    h_g_analytic_one.continuousAt
  -- f_ext agrees with -deriv h / h in a punctured neighborhood of 1
  have h_ζ_ne : ∀ᶠ s in 𝓝[≠] 1, riemannZeta s ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds riemannZeta_eventually_ne_zero_nhds_one
  have h_f_ext_eq_g : f_ext =ᶠ[𝓝[≠] 1] (fun s ↦ -deriv h s / h s) := by
    filter_upwards [h_ζ_ne, self_mem_nhdsWithin (a := (1 : ℂ)) (s := {1}ᶜ)]
      with s hζ_ne hs_ne
    have hs_ne_one : s ≠ 1 := hs_ne
    have h_deriv_eq : deriv h s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      have h_loc : h =ᶠ[𝓝 s] (fun t ↦ (t - 1) * riemannZeta t) := by
        filter_upwards [eventually_ne_nhds hs_ne_one] with x hx
        simp [h, Function.update_of_ne hx]
      have h_g_diff : DifferentiableAt ℂ (fun t ↦ (t - 1) * riemannZeta t) s :=
        ((differentiableAt_id (𝕜 := ℂ)).sub (differentiableAt_const (𝕜 := ℂ) (1 : ℂ))).mul
          (differentiableAt_riemannZeta hs_ne_one)
      have h_deriv_g : deriv (fun t ↦ (t - 1) * riemannZeta t) s =
          riemannZeta s + (s - 1) * deriv riemannZeta s := by
        have h1 : deriv (fun t : ℂ ↦ t - 1) s = 1 := by
          simp [deriv_id'', deriv_const]
        have h2 : (fun t : ℂ ↦ t - 1) s = s - 1 := rfl
        have h3 : DifferentiableAt ℂ (fun t : ℂ ↦ t - 1) s := by
          apply DifferentiableAt.sub
          · exact differentiableAt_id
          · exact differentiableAt_const 1
        have h4 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs_ne_one
        have h5 : deriv (fun t ↦ (t - 1) * riemannZeta t) s =
            deriv (fun t ↦ t - 1) s * riemannZeta s + (fun t ↦ t - 1) s * deriv riemannZeta s := by
          apply deriv_mul h3 h4
        rw [h5]
        simp [h1]
      calc
        deriv h s = deriv (fun t ↦ (t - 1) * riemannZeta t) s :=
          (h_g_diff.hasDerivAt.congr_of_eventuallyEq h_loc).deriv
        _ = riemannZeta s + (s - 1) * deriv riemannZeta s := h_deriv_g
    have h_val_eq : h s = (s - 1) * riemannZeta s := by
      simp [h, Function.update_of_ne hs_ne_one]
    calc
      f_ext s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) := rfl
      _ = -(deriv h s / h s) := by
        rw [h_deriv_eq, h_val_eq]
        have h : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne_one
        field_simp [h, hζ_ne]
        ring_nf
      _ = -deriv h s / h s := by ring
  -- Therefore the limit of f_ext at 1 is -γ
  have h_lim : Tendsto f_ext (𝓝[≠] (1 : ℂ))
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have h_g_lim_punct : Tendsto (fun s ↦ -deriv h s / h s) (𝓝[≠] 1)
        (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
      have h_tendsto : Tendsto (fun s ↦ -deriv h s / h s) (𝓝 1)
          (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
        have h1 : Tendsto (fun s ↦ -deriv h s / h s) (𝓝 1) (𝓝 (-deriv h 1 / h 1)) := h_g_cont_one
        simpa [h_one_val, h_deriv_one] using h1
      exact h_tendsto.mono_left nhdsWithin_le_nhds
    exact Tendsto.congr' h_f_ext_eq_g.symm h_g_lim_punct
  -- Now prove continuity on H_set
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1
    have h_subset : H_set \ {1} ⊆ {1}ᶜ := fun x hx ↦ hx.2
    have h_filter : 𝓝[H_set \ {1}] (1 : ℂ) ≤ 𝓝[≠] (1 : ℂ) :=
      nhdsWithin_mono _ h_subset
    exact continuousWithinAt_update_same.2 (h_lim.mono_left h_filter)
  · have h_f_ext_cont : ContinuousAt f_ext s := by
      dsimp [f_ext]
      have hζ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
      have hζ_cont : ContinuousAt riemannZeta s := hζ_diff.continuousAt
      have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
      have hderivζ_cont : ContinuousAt (deriv riemannZeta) s := by
        have h_an : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := analyticOn_riemannZeta
        have h_cd : ContDiffOn ℂ ⊤ riemannZeta {1}ᶜ :=
          h_an.contDiffOn isOpen_compl_singleton.uniqueDiffOn
        have hderiv_cont : ContinuousOn (deriv riemannZeta) {1}ᶜ :=
          h_cd.continuousOn_deriv_of_isOpen isOpen_compl_singleton le_top
        have hs_mem : s ∈ ({1}ᶜ : Set ℂ) := hs1
        exact hderiv_cont s hs_mem |>.continuousAt (isOpen_compl_singleton.mem_nhds hs_mem)
      have hlog_cont : ContinuousAt (fun t ↦ -deriv riemannZeta t / riemannZeta t) s := by
        have h1 : ContinuousAt (fun t ↦ deriv riemannZeta t / riemannZeta t) s := by
          apply ContinuousAt.div hderivζ_cont hζ_cont hζ_ne
        have h_eq : (fun t : ℂ ↦ -deriv riemannZeta t / riemannZeta t) = (fun t ↦ -(deriv riemannZeta t / riemannZeta t)) := by
          funext t; ring
        rw [h_eq]
        exact h1.neg
      have hinv_cont : ContinuousAt (fun t ↦ 1 / (t - 1)) s := by
        refine ContinuousAt.div continuousAt_const
          (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hs1)
      exact ContinuousAt.sub hlog_cont hinv_cont
    have h_eventually : G_weakPNT =ᶠ[𝓝 s] f_ext := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with t ht
      have ht_ne : t ≠ 1 := ht
      simp only [G_weakPNT, f_ext, ht_ne, ↓reduceIte]
    have h_tendsto_f : Tendsto f_ext (𝓝 s) (𝓝 (f_ext s)) := h_f_ext_cont.tendsto
    have h_val : G_weakPNT s = f_ext s := by
      have hs_ne : s ≠ 1 := hs1
      simp only [G_weakPNT, f_ext, hs_ne, ↓reduceIte]
    have h_tendsto_G : Tendsto G_weakPNT (𝓝 s) (𝓝 (f_ext s)) :=
      Tendsto.congr' h_eventually.symm h_tendsto_f
    have h_cwa : Tendsto (Function.update f_ext 1 (-(Real.eulerMascheroniConstant : ℂ)))
        (𝓝[{s | 1 ≤ s.re}] s) (𝓝 ((Function.update f_ext 1 (-(Real.eulerMascheroniConstant : ℂ))) s)) := by
      rw [← hG_eq, h_val]
      exact h_tendsto_G.mono_left nhdsWithin_le_nhds
    exact h_cwa


/-- The weak PNT: (1/N)∑_{n<N} Λ(n) → 1 -/
theorem WeakPNT : Tendsto (fun N : ℕ => cumsum vonMangoldt N / (N : ℝ))
    atTop (nhds 1) := by
  refine WienerIkeharaTheorem vonMangoldt (fun n => @vonMangoldt_nonneg n) ?_ vonMangoldt_cheby 1 G_weakPNT G_continuous ?_
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
