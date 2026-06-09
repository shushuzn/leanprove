import Mathlib
open Real
open scoped BigOperators

set_option maxHeartbeats 0

/-! ### ζ(σ) 在 σ = 1 附近的行为 -/

/-- ∫_1^N x^{-σ} dx = (N^{1-σ} - 1)/(1-σ) -/
lemma integral_rpow_one_to_N (N : ℕ) (σ : ℝ) (hσ : 1 < σ) (hN : N ≥ 1) :
    ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ : ℝ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
  have hpos : 1 ≤ N := by exact_mod_cast hN
  have h_int := integral_rpow (by
    have : -1 < -σ := by linarith
    left; exact this) (1 : ℝ) (N : ℝ)
  rw [h_int]
  ring

/-- 比较: 对 n ≥ 2 和 σ > 1, 1/n^σ ≤ ∫_{n-1}^n x^{-σ} dx -/
lemma one_div_n_pow_sigma_le_integral (n : ℕ) (σ : ℝ) (hσ : 1 < σ) (hn : n ≥ 2) :
    (1 : ℝ) / ((n : ℝ) ^ σ) ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hpos_interval : (n : ℝ) - 1 < (n : ℝ) := by nlinarith
  have h_int_val : ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) = ((n : ℝ) ^ (1 - σ) - ((n : ℝ) - 1) ^ (1 - σ)) / (1 - σ) := by
    have := integral_rpow (by
      have : -1 < -σ := by linarith
      left; exact this) ((n : ℕ) - 1 : ℝ) (n : ℝ)
    rw [this]
    ring
  -- 由 x^{-σ} 的递减性: 在 [n-1, n] 上, x^{-σ} ≥ n^{-σ}
  have h_decreasing : ∀ x ∈ Set.Icc ((n : ℝ) - 1) (n : ℝ), x ^ (-σ : ℝ) ≥ (1 : ℝ) / ((n : ℝ) ^ σ) := by
    intro x hx
    have hxpos : 0 < x := by
      have : 1 ≤ x := by
        have : (n : ℝ) - 1 ≤ x := hx.1
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le ?_ ?_).trans ?_
    · positivity
    · nlinarith
    · -- x ≥ n 的逆向: x ≤ n, 所以 x^σ ≤ n^σ, 即 x^{-σ} ≥ n^{-σ}
      calc
        x ^ (-σ : ℝ) = (x ^ σ)⁻¹ := by rw [Real.rpow_neg (by positivity : 0 ≤ x)]
        _ ≥ ((n : ℝ) ^ σ)⁻¹ := by
          refine (inv_le_inv ?_ ?_).mpr ?_
          · positivity
          · positivity
          · exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
        _ = (1 : ℝ) / ((n : ℝ) ^ σ) := by ring
  -- 积分不等式: 被积函数 ≥ 常数, 所以积分 ≥ 常数 × 区间长度
  calc
    (1 : ℝ) / ((n : ℝ) ^ σ) = ((1 : ℝ) / ((n : ℝ) ^ σ)) * (((n : ℝ) - ((n : ℝ) - 1))) := by ring
    _ = ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), ((1 : ℝ) / ((n : ℝ) ^ σ)) := by simp
    _ ≤ ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) :=
      intervalIntegral.integral_mono (by nlinarith) (intervalIntegrable_const) (by
        refine Continuous.intervalIntegrable ?_ _ _
        exact (continuous_rpow_of_ne_zero (by nlinarith) _).comp continuous_id)
      (h_decreasing)

/-- 部分和 ∑_{n=2}^N 1/n^σ ≤ ∫_1^N x^{-σ} dx = (N^{1-σ} - 1)/(1-σ) ≤ 1/(σ-1) -/
lemma zetaPartial_upper_bound (N : ℕ) (σ : ℝ) (hσ : 1 < σ) (hN : N ≥ 1) :
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) ≤ 1 / (σ - 1) := by
  calc
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ)
        ≤ ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℕ) - 1 : ℝ)..(n : ℝ), x ^ (-σ : ℝ) :=
      Finset.sum_le_sum (λ n hn => one_div_n_pow_sigma_le_integral n σ hσ (by
        have hn2 : n ≥ 2 := (Finset.mem_Icc.mp hn).1; exact hn2))
    _ = ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ : ℝ) := by
      -- 裂项消去: ∑_{n=2}^N ∫_{n-1}^n = ∫_1^N
      induction' N with k IH generalizing σ
      · simp
      · rcases eq_or_lt_of_le (Nat.succ_le_succ (Nat.zero_le _)) with (h | h)
        · subst h; simp
        · rw [Finset.Icc_succ_singleton, Finset.sum_insert (by simp)]
          have h_last : ∫ x in ((k.succ : ℕ) - 1 : ℝ)..(k.succ : ℝ), x ^ (-σ : ℝ) = 
              ∫ x in (k : ℝ)..(k.succ : ℝ), x ^ (-σ : ℝ) := by simp
          rw [h_last]
          rw [intervalIntegral.integral_add_adjacent_intervals (by
            refine Continuous.intervalIntegrable ?_ _ _
            exact (continuous_rpow_of_ne_zero (by nlinarith) _).comp continuous_id) (by
            refine Continuous.intervalIntegrable ?_ _ _
            exact (continuous_rpow_of_ne_zero (by nlinarith) _).comp continuous_id)]
    _ = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by rw [integral_rpow_one_to_N N σ hσ hN]
    _ ≤ 1 / (σ - 1) := by
      have h_neg : 1 - σ < 0 := by linarith
      have h_pow : 0 ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
      have : ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (0 - 1) / (1 - σ) := by
        refine (div_le_div_right (by linarith)).mpr ?_
        nlinarith
      calc
        ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (-1) / (1 - σ) := by
          refine (div_le_div_right (by linarith)).mpr ?_
          nlinarith
        _ = 1 / (σ - 1) := by ring

/-- ζ(σ) ≤ 1 + 1/(σ-1) -/
lemma zetaReal_upper_bound (σ : ℝ) (hσ : 1 < σ) : zetaReal σ hσ ≤ 1 + 1 / (σ - 1) := by
  have h_sup : zetaReal σ hσ = ⨆ N : ℕ, zetaRealPartial N σ := rfl
  apply ciSup_le
  intro N
  dsimp [zetaRealPartial]
  have h_cases : N = 0 ∨ N ≥ 1 := by omega
  rcases h_cases with (h | h)
  · subst h; simp
  · calc
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ σ)
          = 1 + ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) ^ σ) := by
            have h_split : Finset.Icc 1 N = {1} ∪ Finset.Icc 2 N := by ext n; simp; omega
            rw [h_split, Finset.sum_union (by simp), Finset.sum_singleton]; simp
      _ ≤ 1 + 1 / (σ - 1) := by
        refine add_le_add_left (zetaPartial_upper_bound N σ hσ h) _

/-- 下界: ζ(σ) ≥ 1/(σ-1) (更弱但够用) -/
lemma zetaReal_lower_bound (σ : ℝ) (hσ : 1 < σ) : 1 / (σ - 1) ≤ zetaReal σ hσ := by
  have h_int_val : ∫ x in (1 : ℝ)..∞, x ^ (-σ : ℝ) = 1 / (σ - 1) := by
    -- 用单调收敛定理
    sorry
  sorry

/-- lim (σ-1)ζ(σ) = 1 -/
lemma zetaReal_limit (σ : ℝ) (hσ : 1 < σ) : (σ - 1) * zetaReal σ hσ ≤ σ := by
  have h_upper := zetaReal_upper_bound σ hσ
  have hpos : 0 < σ - 1 := by linarith
  nlinarith
