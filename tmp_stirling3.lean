
import Mathlib
open Real Finset
open scoped BigOperators

-- Stirling bound: ∑_{n=1}^{N} log n = N·log N - N + O(log N)
lemma stirling_bound (N : ℕ) (hN : N ≥ 1) : |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 1 := by
  have h_log_nonneg : ∀ (n : ℕ), 1 ≤ n → 0 ≤ Real.log (n : ℝ) := by
    intro n hn; exact Real.log_nonneg (by exact_mod_cast hn)
  
  -- ∫_1^N log t dt ≤ ∑_{n=1}^N log n (since log is increasing)
  have h_bound_low : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
    have h_int_low : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
      calc
        ∫ t in (1 : ℝ)..(N : ℝ), Real.log t ≤ ∑ n ∈ Icc 1 N, ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
          -- ∫_1^N = ∑_{n=1}^{N-1} ∫_n^{n+1}
          -- This is an equality, not inequality
          rw [intervalIntegral.integral_add_adjacent_intervals]
          sorry
        _ ≤ ∑ n ∈ Icc 1 N, Real.log (n+1 : ℝ) := by
          -- For t ∈ [n, n+1], log t ≤ log(n+1) (since log is increasing)
          refine Finset.sum_le_sum (λ n hn => ?_)
          have : ∀ t ∈ Set.Icc (n : ℝ) (n+1 : ℝ), Real.log t ≤ Real.log ((n : ℝ) + 1) := ...
          ...
    have h_int_val : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
      rw [integral_log]; ring
    rw [h_int_val] at h_int_low; linarith
  
  -- ∑_{n=1}^N log n ≤ ∫_1^N log t dt + log N
  have h_bound_high : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 + Real.log (N : ℝ) := by
    have h_int_high : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ ∫ t in (1 : ℝ)..(N : ℝ), Real.log t + Real.log (N : ℝ) := by
      calc
        ∑ n ∈ Icc 1 N, Real.log (n : ℝ) = Real.log 1 + ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by
          have : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
          rw [this, Finset.sum_union (by simp), Finset.sum_singleton]; simp
        _ = ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by simp
        _ ≤ ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t + Real.log (N : ℝ) := ...
        _ ≤ ∫ t in (1 : ℝ)..(N : ℝ), Real.log t + Real.log (N : ℝ) := ...
    sorry
  
  rcases h_bound_low, h_bound_high with ⟨hlow, hhigh⟩
  rw [abs_le]
  constructor
  · linarith
  · linarith
