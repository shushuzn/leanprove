
import Mathlib
open Finset
open scoped BigOperators

example (N : ℕ) : ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * (N / n : ℕ) = ∑ m ∈ Icc 1 N, Real.log (m : ℝ) := by
  calc
    ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * (N / n : ℕ) = ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * (∑ m ∈ Icc 1 (N / n), 1) := by simp
    _ = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / n), (ArithmeticFunction.vonMangoldt n : ℝ) := by simp [Finset.mul_sum]
    _ = ∑ (x : ℕ × ℕ) in (Finset.Icc 1 N).product (Finset.Icc 1 N), if x.1 * x.2 ≤ N then (ArithmeticFunction.vonMangoldt x.1 : ℝ) else 0 := by
      sorry
    _ = ∑ m ∈ Icc 1 N, ∑ d ∈ divisors m, (ArithmeticFunction.vonMangoldt d : ℝ) := by
      sorry
    _ = ∑ m ∈ Icc 1 N, Real.log (m : ℝ) := by
      simp [ArithmeticFunction.vonMangoldt_sum, ArithmeticFunction.vonMangoldt_sum_divisors]
