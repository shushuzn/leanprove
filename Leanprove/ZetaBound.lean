import Mathlib
open Real
open scoped BigOperators

set_option maxHeartbeats 0

/-- ζ(σ) ≤ 1 + 1/(σ-1) 对 σ > 1 -/
lemma zeta_upper_bound (σ : ℝ) (hσ : 1 < σ) : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 + 1 / (σ - 1) := by
  have hpos_sq : ∀ n : ℕ, (n : ℝ) ^ σ > 0 := by
    intro n; by_cases hn : n = 0; subst hn; norm_num; positivity
  have h_summable : Summable (λ n : ℕ => (1 : ℝ) / ((n : ℝ) ^ σ)) := by
    refine (Real.summable_nat_rpow.mpr (by linarith)).of_nonneg_of_le (λ n => ?_) (λ n => ?_)
    · positivity; · simp [Real.rpow_neg (by exact_mod_cast (Nat.zero_le n) : 0 ≤ (n : ℝ))]
  -- 对任意 N ≥ 1, 部分和 ≤ 1 + 1/(σ-1)
  have h_partial (N : ℕ) (hN : N ≥ 1) : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 + 1 / (σ - 1) := by
    calc
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ) = 1 + ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
        have h_split : Finset.Icc 1 N = {1} ∪ Finset.Icc 2 N := by ext n; simp; omega
        rw [h_split, Finset.sum_union (by simp), Finset.sum_singleton]; simp
      _ ≤ 1 + ∑ n ∈ Finset.Icc 2 N, (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by
        refine add_le_add_left (Finset.sum_le_sum (λ n hn => ?_)) _
        have hn2 : n ≥ 2 := (Finset.mem_Icc.mp hn).1
        have h_ineq : (1 : ℝ) / ((n : ℝ) ^ σ) ≤ (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by
          -- 被积函数 x^{-σ} 递减 → ∫_{n-1}^n x^{-σ} dx ≥ n^{-σ}
          -- 且 ∫ = ((n-1)^{1-σ} - n^{1-σ})/(σ-1)
          have h_int_val : ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) = (((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) / (σ - 1) := by
            have h := integral_rpow (by
              have : (-1 : ℝ) < -σ := by linarith; left; exact this) (((n : ℕ) - 1 : ℝ)) (n : ℝ)
            rw [h, show (-σ : ℝ) + 1 = (1 : ℝ) - σ by ring, show (1 - σ) + 1 = 2 - σ by ring]
            ring
          rw [← h_int_val]
          have h_int_ineq : (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) := by
            have h_int_const : IntervalIntegrable (λ _ : ℝ => (1 : ℝ) / ((n : ℝ) ^ σ)) volume (((n : ℕ) - 1 : ℝ)) (n : ℝ) :=
              intervalIntegrable_const
            have h_int_f : IntervalIntegrable (λ x : ℝ => x ^ (-σ : ℝ)) volume (((n : ℕ) - 1 : ℝ)) (n : ℝ) :=
              (continuous_rpow_of_ne_zero (by nlinarith) _).intervalIntegrable _ _
            have h_ineq_on : ∀ x ∈ Set.Icc (((n : ℕ) - 1 : ℝ)) (n : ℝ), (1 : ℝ) / ((n : ℝ) ^ σ) ≤ x ^ (-σ : ℝ) := by
              intro x hx
              have hxpos : 0 < x := by nlinarith
              calc
                (1 : ℝ) / ((n : ℝ) ^ σ) = ((n : ℝ) ^ (-σ : ℝ)) := by
                  simp [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))]
                _ ≤ x ^ (-σ : ℝ) := by
                  refine (Real.rpow_le_rpow_of_exponent_le (by positivity) hx.2).trans ?_
                  exact le_refl _
            calc
              (1 : ℝ) / ((n : ℝ) ^ σ) = ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), (1 : ℝ) / ((n : ℝ) ^ σ) := by simp
              _ ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) :=
                intervalIntegral.integral_mono (by nlinarith) h_int_const h_int_f h_ineq_on
          exact h_int_ineq
        exact h_ineq
      _ = 1 + (1 / (σ - 1) - ((N : ℝ) ^ (1 - σ)) / (σ - 1)) := by
        induction' N with k IH generalizing σ
        · omega
        · rw [Finset.Icc_succ_singleton, Finset.sum_insert (by simp), IH (by omega)]
          ring
      _ ≤ 1 + 1 / (σ - 1) := by
        have h_nonneg : 0 ≤ ((N : ℝ) ^ (1 - σ)) / (σ - 1) := by
          positivity
        nlinarith
  -- 从部分和到级数和
  have h_tsum : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ) = ⨆ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
    apply tsum_eq_iSup_sum_of_nonneg (λ n => by positivity)
  have h_range_to_Icc (N : ℕ) : ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
    refine Finset.sum_le_sum_of_subset (λ n hn => ?_)
    rw [Finset.mem_range] at hn
    have hn' : n ≤ N := hn
    by_cases hn0 : n = 0; subst hn0; simp; exact Finset.mem_Icc.mpr ⟨by omega, hn'⟩
  apply ciSup_le
  intro N
  calc
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ) := h_range_to_Icc N
    _ ≤ 1 + 1 / (σ - 1) := h_partial N (by
      by_cases h : N ≥ 1; exact h; omega)
