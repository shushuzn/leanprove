
import Mathlib
open Real Finset
open scoped BigOperators

-- Stirling bound: ∑_{n=1}^{N} log n = N·log N - N + O(log N)
lemma sum_log_ Stirling (N : ℕ) (hN : N ≥ 1) : |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 2 := by
  have h_int_low : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≥ ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) := by
    -- ∫_1^N log t dt ≤ ∑_{n=1}^N log n
    calc
      ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≥ ∫ t in (1 : ℝ)..(N : ℝ), Real.log t := by
        -- 对单调递减函数⋯不对，log t 是递增的
        -- 反了: log n 递增, 所以 ∫_n^{n+1} log t dt ≤ log(n+1)
        -- 更精确: ∫_1^{N+1} log t dt ≤ ∑_{n=1}^N log (n+1)
        sorry
      _ = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
        rw [integral_log]
        simp
  sorry
