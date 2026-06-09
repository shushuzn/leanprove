import Mathlib
open Real Finset
open scoped BigOperators

lemma sum_log_stirling (N : ℕ) (hN : N ≥ 1) : |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 1 := by
  have h_int_val : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]; ring
  -- For increasing f: ∫_1^N f ≤ ∑_{n=1}^N f(n) ≤ ∫_1^N f + f(N)
  have h_inc : ∀ (a b : ℝ), a ≤ b → Real.log a ≤ Real.log b := Real.log_le_log
  -- Actually we need integral bounds using monotonicity
  -- ∫_1^N log t dt ≤ ∑_{n=1}^N log n (since log is increasing, f(n) ≥ ∫_{n}^{n+1} f)
  have h_low : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
    calc
      (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 = ∫ t in (1 : ℝ)..(N : ℝ), Real.log t := by rw [h_int_val]
      _ ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
        -- We need to compare the integral with the sum
        -- For increasing f: ∫_n^{n+1} f(t) dt ≤ f(n+1) and f(n) ≤ ∫_n^{n+1} f(t) dt
        -- So ∫_1^N f ≤ ∑_{n=2}^N f(n) = ∑_{n=1}^N f(n) (since f(1)=0)
        -- Using the property: ∫_a^{a+1} f(t) dt ≤ f(a+1) for increasing f
        calc
          ∫ t in (1 : ℝ)..(N : ℝ), Real.log t
              = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
                induction' N with k ih
                · simp
                · rw [Finset.Icc_succ_singleton?]
          _ ≤ ∑ n ∈ Icc 1 (N-1), Real.log (n+1 : ℝ) := by
            refine Finset.sum_le_sum (λ n hn => ?_)
            have : ∀ t ∈ Set.Icc (n : ℝ) (n+1 : ℝ), Real.log t ≤ Real.log (n+1 : ℝ) := by
              intro t ht; exact Real.log_le_log (by nlinarith [ht.1]) (by nlinarith [ht.2])
            -- use intervalIntegral.integral_mono
            sorry
          _ = ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by
            -- shift index
            sorry
          _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
            have : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
            rw [this, Finset.sum_union (by simp), Finset.sum_singleton]; simp
  sorry
