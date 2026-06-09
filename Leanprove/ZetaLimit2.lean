import Mathlib
open Real Finset
open scoped BigOperators

set_option maxHeartbeats 0

/-- ∫_1^N x^{-σ} dx = (N^{1-σ} - 1)/(1-σ) -/
lemma integral_x_pow_neg (N : ℕ) (σ : ℝ) (hσ : 1 < σ) (hN : N ≥ 1) :
    ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ : ℝ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
  have h_int := integral_rpow (by
    have : (-1 : ℝ) < -σ := by linarith; left; exact this) (1 : ℝ) (N : ℝ)
  rw [h_int]; ring

/-- 单调性: 对 x ≤ y, x^{-σ} ≥ y^{-σ} (因为 -σ < 0) -/
lemma x_pow_neg_anti (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (σ : ℝ) (hσ : 1 < σ) :
    x ^ (-σ : ℝ) ≥ y ^ (-σ : ℝ) := by
  refine (Real.rpow_le_rpow_of_exponent_le (by positivity) ?_).trans ?_
  · exact hxy
  · exact le_refl _

/-- 比较: n^{-σ} ≤ ∫_{n-1}^n x^{-σ} dx, 对 n ≥ 2 -/
lemma n_pow_neg_le_integral (n : ℕ) (σ : ℝ) (hσ : 1 < σ) (hn : n ≥ 2) :
    (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) := by
  have hpos_n : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have h_int_const : IntervalIntegrable (λ _ : ℝ => (1 : ℝ) / ((n : ℝ) ^ σ)) volume ((n : ℕ) - 1 : ℝ) (n : ℝ) :=
    intervalIntegrable_const
  have h_int_f : IntervalIntegrable (λ x : ℝ => x ^ (-σ : ℝ)) volume ((n : ℕ) - 1 : ℝ) (n : ℝ) :=
    (continuous_rpow_of_ne_zero (by nlinarith) _).intervalIntegrable _ _
  have h_ineq : ∀ x ∈ Set.Icc (((n : ℕ) - 1 : ℝ)) (n : ℝ), (1 : ℝ) / ((n : ℝ) ^ σ) ≤ x ^ (-σ : ℝ) := by
    intro x hx
    have hxpos : 0 < x := by
      have : (n : ℝ) - 1 ≤ x := hx.1; have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hx_le_n : x ≤ (n : ℝ) := hx.2
    calc
      (1 : ℝ) / ((n : ℝ) ^ σ) = ((n : ℝ) ^ (-σ : ℝ)) := by simp [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))]
      _ ≤ x ^ (-σ : ℝ) := x_pow_neg_anti x (n : ℝ) hxpos hx_le_n σ hσ
  calc
    (1 : ℝ) / ((n : ℝ) ^ σ) = ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), (1 : ℝ) / ((n : ℝ) ^ σ) := by simp
    _ ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) :=
      intervalIntegral.integral_mono (by nlinarith) h_int_const h_int_f h_ineq

/-- 裂项: ∑_{n=2}^N ∫_{n-1}^n f = ∫_1^N f -/
lemma sum_int_telescope (N : ℕ) (f : ℝ → ℝ) (hN : N ≥ 1) (hf : ∀ n : ℕ, n ≥ 1 → n ≤ N → 
    IntervalIntegrable f volume ((n : ℕ) - 1 : ℝ) (n : ℝ)) : 
    ∑ n ∈ Icc 2 N, ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), f x = ∫ x in (1 : ℝ)..(N : ℝ), f x := by
  induction' N with k IH
  · omega
  · by_cases hk : k < 2
    · omega
    · have hk1 : 1 ≤ k := by omega
      have hk2 : 2 ≤ k := by omega
      rw [Finset.Icc_succ_singleton, Finset.sum_insert (by
        intro h; have := Finset.mem_Icc.mp h; omega)]
      have h_last : ∫ x in ((k.succ : ℕ) - 1 : ℝ)..(k.succ : ℝ), f x = ∫ x in (k : ℝ)..(k.succ : ℝ), f x := by simp
      rw [h_last]
      rw [IH (by omega) (λ n hn1 hn2 => hf n hn1 (by omega)), intervalIntegral.integral_add_adjacent_intervals
        (hf 1 (by omega) (by omega)) (hf k hk1 (by omega))]

/-- 部分和上界: ∑_{n=2}^N 1/n^σ ≤ ∫_1^N x^{-σ} dx ≤ 1/(σ-1) -/
lemma zeta_partial_upper (N : ℕ) (σ : ℝ) (hσ : 1 < σ) (hN : N ≥ 1) : 
    ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 / (σ - 1) := by
  calc
    ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ)
        ≤ ∑ n ∈ Icc 2 N, ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) :=
      Finset.sum_le_sum (λ n hn => n_pow_neg_le_integral n σ hσ (by
        have hn2 : n ≥ 2 := (Finset.mem_Icc.mp hn).1; exact hn2))
    _ = ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ : ℝ) := by
      refine sum_int_telescope N (λ x => x ^ (-σ : ℝ)) hN (λ n hn1 hn2 => ?_)
      have hnpos : (n : ℝ) - 1 < (n : ℝ) := by nlinarith
      exact (continuous_rpow_of_ne_zero (by nlinarith) _).intervalIntegrable _ _
    _ = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by rw [integral_x_pow_neg N σ hσ hN]
    _ ≤ 1 / (σ - 1) := by
      have h_neg : 1 - σ < 0 := by linarith
      have h_pow_nonneg : 0 ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
      have : ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (-1) / (1 - σ) := by
        refine (div_le_div_right (by linarith)).mpr ?_
        nlinarith
      calc
        ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (-1) / (1 - σ) := this
        _ = 1 / (σ - 1) := by ring

/-- ζ(σ) ≤ 1 + 1/(σ-1) -/
lemma zeta_upper (σ : ℝ) (hσ : 1 < σ) : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ)) ≤ 1 + 1 / (σ - 1) := by
  have h_sum : ∀ N : ℕ, N ≥ 1 → ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 / (σ - 1) :=
    λ N hN => zeta_partial_upper N σ hσ hN
  -- 对任意 N ≥ 1, 部分和 ≤ 1 + 1/(σ-1)
  -- 因此极限也 ≤ 1 + 1/(σ-1)
  sorry
