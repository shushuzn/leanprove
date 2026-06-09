import Mathlib
open Real Finset Set Filter
open scoped BigOperators Topology

set_option maxHeartbeats 0

/-! ### Phase IV-B: (σ-1)ζ(σ) → 1 -/

/-- x ≤ y, ε < 0 ⇒ x^ε ≥ y^ε (x,y > 0) -/
lemma rpow_anti (x y ε : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hε : ε < 0) : x ^ ε ≥ y ^ ε := by
  have hpos_neg : 0 < -ε := by linarith
  have hx_le_y_neg : x ^ (-ε) ≤ y ^ (-ε) := Real.rpow_le_rpow (by positivity) hxy (by linarith)
  have hxpos_neg : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx _
  have hypos_neg : 0 < y ^ (-ε) := Real.rpow_pos_of_pos hy _
  have h_inv : (y ^ (-ε))⁻¹ ≤ (x ^ (-ε))⁻¹ := by
    simpa using (one_div_le_one_div hypos_neg hxpos_neg).mpr hx_le_y_neg
  calc
    x ^ ε = (x ^ (-(-ε))) := by simp
    _ = (x ^ (-ε))⁻¹ := by rw [Real.rpow_neg (by positivity : 0 ≤ x)]
    _ ≥ (y ^ (-ε))⁻¹ := h_inv
    _ = y ^ (-(-ε)) := by rw [← Real.rpow_neg (by positivity : 0 ≤ y)]
    _ = y ^ ε := by simp

/-- MVT 给出的不等式: (n-1)^{1-σ} - n^{1-σ} ≥ (σ-1)·n^{-σ} -/
lemma mvt_ineq (n : ℕ) (σ : ℝ) (hσ : 1 < σ) (hn : n ≥ 2) : 
    ((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) ≥ (σ - 1) * ((n : ℝ) ^ (-σ)) := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha_pos : 0 < (n : ℝ) - 1 := by nlinarith
  have hb_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have h_lt : (n : ℝ) - 1 < (n : ℝ) := by nlinarith
  set f := λ (x : ℝ) => x ^ (1 - σ) with hf
  have hf_diff : ∀ x ∈ Set.Ioo ((n : ℝ) - 1) (n : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    have hxpos : 0 < x := by
      have hx_low : (n : ℝ) - 1 < x := hx.1
      nlinarith
    exact (hasDerivAt_rpow_const (Or.inl hxpos.ne')).differentiableAt
  have hf_cont : ∀ x ∈ Set.Icc ((n : ℝ) - 1) (n : ℝ), ContinuousAt f x := by
    intro x hx
    have hxpos : 0 < x := by
      have hx_low : (n : ℝ) - 1 ≤ x := hx.1
      nlinarith
    exact (hasDerivAt_rpow_const (Or.inl hxpos.ne')).continuousAt
  have hf_diff_on : DifferentiableOn ℝ f (Set.Ioo ((n : ℝ) - 1) (n : ℝ)) := by
    intro x hx; exact (hf_diff x hx).differentiableWithinAt
  have hf_cont_on : ContinuousOn f (Set.Icc ((n : ℝ) - 1) (n : ℝ)) := by
    intro x hx; exact (hf_cont x hx).continuousWithinAt
  rcases exists_deriv_eq_slope f h_lt hf_cont_on hf_diff_on with ⟨c, hc, hc_deriv⟩
  · have h_deriv : deriv f c = (1 - σ) * (c ^ (-σ)) := by
      have h_hasDeriv : HasDerivAt f ((1 - σ) * (c ^ (1 - σ - 1))) c := by
        dsimp [f]
        have hcpos : c ≠ 0 := by
          have : (n : ℝ) - 1 < c := hc.1; nlinarith
        exact hasDerivAt_rpow_const (Or.inl hcpos)
      rw [h_hasDeriv.deriv]
      have : (1 - σ - 1 : ℝ) = -σ := by ring
      simp [this]
    have h_mvt : f (n : ℝ) - f ((n : ℝ) - 1) = deriv f c := by
      have h_deriv_eq : deriv f c = (f (n : ℝ) - f ((n : ℝ) - 1)) / ((n : ℝ) - ((n : ℝ) - 1)) := hc_deriv
      have h_sub : (n : ℝ) - ((n : ℝ) - 1) = 1 := by ring
      rw [h_sub, div_one] at h_deriv_eq
      linarith
    have h_main : f ((n : ℝ) - 1) - f (n : ℝ) = (σ - 1) * (c ^ (-σ)) := by
      calc
        f ((n : ℝ) - 1) - f (n : ℝ) = -(f (n : ℝ) - f ((n : ℝ) - 1)) := by ring
        _ = -deriv f c := by rw [h_mvt]
        _ = -((1 - σ) * (c ^ (-σ))) := by rw [h_deriv]
        _ = (σ - 1) * (c ^ (-σ)) := by ring
    have h_c_le_n : c ≤ (n : ℝ) := by
      have : c < (n : ℝ) := hc.2; exact this.le
    have h_c_pow_ge : c ^ (-σ) ≥ (n : ℝ) ^ (-σ) :=
      rpow_anti c (n : ℝ) (-σ) (by
        have : (n : ℝ) - 1 < c := hc.1; nlinarith) hb_pos h_c_le_n (by linarith)
    calc
      ((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) = f ((n : ℝ) - 1) - f (n : ℝ) := rfl
      _ = (σ - 1) * (c ^ (-σ)) := h_main
      _ ≥ (σ - 1) * ((n : ℝ) ^ (-σ)) := mul_le_mul_of_nonneg_left h_c_pow_ge (by linarith)

/-- n^{-σ} ≤ ((n-1)^{1-σ} - n^{1-σ})/(σ-1) (由 MVT 推导) -/
lemma n_pow_le_telescope (n : ℕ) (σ : ℝ) (hσ : 1 < σ) (hn : n ≥ 2) :
    (1 : ℝ) / ((n : ℝ) ^ σ) ≤ (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by
  have hpos : 0 < σ - 1 := by linarith
  have h := mvt_ineq n σ hσ hn
  have hcalc : (σ - 1) * ((n : ℝ) ^ (-σ)) ≤ ((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) := h
  have hdiv : (n : ℝ) ^ (-σ) ≤ (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by
    calc
      (n : ℝ) ^ (-σ) = ((σ - 1) * ((n : ℝ) ^ (-σ))) * (σ - 1)⁻¹ := by field_simp [hpos.ne']
      _ ≤ (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) * (σ - 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hcalc (by positivity : 0 ≤ (σ - 1)⁻¹)
      _ = (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by ring
  calc
    (1 : ℝ) / ((n : ℝ) ^ σ) = (n : ℝ) ^ (-σ) := by
      simp [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))]
    _ ≤ (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := hdiv

/-- ∑_{n=2}^N n^{-σ} ≤ 1/(σ-1) -/
lemma sum_bound_upper (N : ℕ) (σ : ℝ) (hσ : 1 < σ) (hN : N ≥ 1) :
    ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 / (σ - 1) := by
  calc
    ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ)
        ≤ ∑ n ∈ Icc 2 N, (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) :=
      Finset.sum_le_sum (λ n hn => n_pow_le_telescope n σ hσ ((Finset.mem_Icc.mp hn).1))
    _ = (1 / (σ - 1)) - ((N : ℝ) ^ (1 - σ)) / (σ - 1) := by
      have hNpos : N ≥ 1 := hN
      refine Nat.le_induction (by
        simp [Real.zero_rpow (by linarith : 1 - σ ≠ 0)])
        (λ k hk hk_IH => ?_) N hNpos
      by_cases hk2 : k ≥ 2
      · have h_insert : Finset.Icc 2 k.succ = (Finset.Icc 2 k) ∪ {k.succ} := by ext n; simp; omega
        have h_disj : Disjoint (Finset.Icc 2 k) ({k.succ} : Finset ℕ) := by simp
        have h_sum_succ : ∑ n ∈ Icc 2 k.succ, (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) =
            (∑ n ∈ Icc 2 k, (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1)) +
            (((k : ℝ) ^ (1 - σ) - ((k : ℝ) + 1) ^ (1 - σ)) / (σ - 1)) := by
          rw [h_insert, Finset.sum_union h_disj, Finset.sum_singleton]
          simp [Nat.cast_succ]
        rw [h_sum_succ, hk_IH]
        have h_eq : (1 / (σ - 1) - ((k : ℝ) ^ (1 - σ)) / (σ - 1)) + 
            (((k : ℝ) ^ (1 - σ) - ((k : ℝ) + 1) ^ (1 - σ)) / (σ - 1)) = 
            1 / (σ - 1) - (((k : ℝ) + 1) ^ (1 - σ)) / (σ - 1) := by
          field_simp [show (σ - 1) ≠ 0 from by linarith]
          nlinarith
        rw [h_eq]
        simp [Nat.cast_succ]
      · -- k = 1: Icc 2 2 = {2}, 验证等式
        have : k = 1 := by omega
        subst this
        -- Icc 2 (1+1) = Icc 2 2 = {2}
        have h_Icc : Finset.Icc 2 (1 + 1 : ℕ) = ({2} : Finset ℕ) := by
          ext n; simp; omega
        rw [h_Icc, Finset.sum_singleton]
        -- (((2:ℝ) - 1)^(1-σ) - (2:ℝ)^(1-σ)) / (σ-1) = (1 - 2^(1-σ)) / (σ-1) = 1/(σ-1) - 2^(1-σ)/(σ-1)
        push_cast
        have h_eq : ((2 : ℝ) - 1) ^ (1 - σ) = 1 := by
          rw [show (2 : ℝ) - 1 = 1 from by ring, Real.one_rpow]
        rw [h_eq]
        field_simp [show (σ - 1 : ℝ) ≠ 0 from by linarith]
    _ ≤ 1 / (σ - 1) := by
      have h_nonneg : 0 ≤ ((N : ℝ) ^ (1 - σ)) / (σ - 1) := by positivity
      nlinarith

/-- ζ(σ) ≤ 1 + 1/(σ-1) -/
lemma zeta_upper_bound (σ : ℝ) (hσ : 1 < σ) : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 + 1 / (σ - 1) := by
  have h_summable : Summable (λ n : ℕ => (1 : ℝ) / ((n : ℝ) ^ σ)) := by
    have : Summable (λ n : ℕ => ((n : ℝ) ^ (-σ : ℝ))) := Real.summable_nat_rpow.mpr (by linarith)
    have h_eq : (λ n : ℕ => (1 : ℝ) / ((n : ℝ) ^ σ)) = (λ n : ℕ => ((n : ℝ) ^ (-σ : ℝ))) := by
      ext n; simp [Real.rpow_neg (by exact_mod_cast (Nat.zero_le n) : 0 ≤ (n : ℝ))]
    rw [h_eq]; exact this
  have h_partial (N : ℕ) : ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 + 1 / (σ - 1) := by
    by_cases hN : N ≤ 1
    · rcases Nat.lt_or_ge N 1 with hN_lt | hN_ge
      · -- N < 1
        interval_cases N
        -- N = 0
        simp
        positivity
      · -- N = 1
        have : N = 1 := by omega
        subst this
        simp
        positivity
    · push_neg at hN
      -- N ≥ 2
      have h_split : Finset.range N = ({0} : Finset ℕ) ∪ Finset.Icc 1 (N - 1) := by
        apply Finset.ext; intro n; simp; omega
      have h_disj : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (N - 1)) := by simp
      have h_split2 : Finset.Icc 1 (N - 1) = ({1} : Finset ℕ) ∪ Finset.Icc 2 (N - 1) := by
        apply Finset.ext; intro n; simp; omega
      have h_disj2 : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (N - 1)) := by simp
      have h_main : (∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ)) = 
          1 + ∑ n ∈ Finset.Icc 2 (N - 1), (1 : ℝ) / ((n : ℝ) ^ σ) := by
        rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
        rw [Real.zero_rpow (by linarith : (σ : ℝ) ≠ 0)]
        rw [zero_add, h_split2, Finset.sum_union h_disj2, Finset.sum_singleton]
        rw [Real.one_rpow]
      rw [h_main]
      apply add_le_add_right
      have hN_sub : N - 1 ≥ 1 := by omega
      exact sum_bound_upper (N - 1) σ hσ hN_sub
  have h_tendsto : Filter.Tendsto (λ N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ)) Filter.atTop
      (𝓝 (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ))) :=
    h_summable.hasSum.tendsto_sum_nat
  exact le_of_tendsto h_tendsto (Filter.eventually_of_forall h_partial)
