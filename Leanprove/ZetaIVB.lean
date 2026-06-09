import Mathlib
open Real Finset
open scoped BigOperators

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
  sorry

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
        rw [h_insert, Finset.sum_union h_disj, Finset.sum_singleton, hk_IH]
        field_simp [show (σ - 1) ≠ 0 from by linarith]
        ring
      · have : k = 1 := by omega
        subst this; simp; field_simp [show (σ - 1) ≠ 0 from by linarith]; ring
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
  have h_nonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) ^ σ) := by
    intro n; positivity
  have h_tsum_eq : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ) = ⨆ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) :=
    tsum_eq_iSup_sum_of_nonneg h_nonneg
  rw [h_tsum_eq]
  apply ciSup_le
  intro N
  calc
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
      refine Finset.sum_le_sum_of_subset (λ n hn => ?_)
      rw [Finset.mem_range] at hn
      by_cases hn0 : n = 0
      · subst hn0; simp
      · exact Finset.mem_Icc.mpr ⟨by omega, hn⟩
    _ = 1 + ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
      have h_split : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
      rw [h_split, Finset.sum_union (by simp), Finset.sum_singleton]; simp
    _ ≤ 1 + 1 / (σ - 1) := add_le_add_left (sum_bound_upper N σ hσ (by omega)) _
