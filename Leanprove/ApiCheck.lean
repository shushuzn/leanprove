/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- ApiCheck.lean: verify Mathlib API names for sum ≤ tsum
-- These are the correct names in Mathlib v4.31.0-rc2

import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped BigOperators
open Finset

-- Test 1: Summable.sum_le_tsum
-- This is the main lemma: sum over finset ≤ tsum, given Summable + nonnegativity
theorem test_Summable_sum_le_tsum (f : ℕ → ℝ) (s : Finset ℕ) (hs : Summable f)
    (h : ∀ i, 0 ≤ f i) : ∑ x ∈ s, f x ≤ tsum f := by
  exact Summable.sum_le_tsum s (fun i _ => h i) hs

-- Test 2: sum_le_hasSum (lower-level version using HasSum)
theorem test_sum_le_hasSum (f : ℕ → ℝ) (s : Finset ℕ) (hs : HasSum f (tsum f))
    (h : ∀ i, 0 ≤ f i) : ∑ x ∈ s, f x ≤ tsum f := by
  exact sum_le_hasSum s (fun i _ => h i) hs

-- Test 3: Summable.of_nonneg_of_le (comparison test for ℝ)
-- THIS LIVES IN Mathlib.Topology.Algebra.InfiniteSum.ENNReal
theorem test_Summable_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f)
    (hg : ∀ i, 0 ≤ g i) (hle : ∀ i, g i ≤ f i) : Summable g := by
  exact Summable.of_nonneg_of_le hg hle hf

-- Test 4: Summable.tsum_le_tsum (monotonicity of tsum)
theorem test_Summable_tsum_le_tsum {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hle : ∀ i, f i ≤ g i) : tsum f ≤ tsum g := by
  exact Summable.tsum_le_tsum hle hf hg

-- Test 5: tsum_nonneg
theorem test_tsum_nonneg {f : ℕ → ℝ} (h : ∀ i, 0 ≤ f i) : 0 ≤ tsum f := by
  exact tsum_nonneg h

-- Test 6: Summable.le_tsum (single element ≤ tsum)
theorem test_Summable_le_tsum (f : ℕ → ℝ) (i : ℕ) (hs : Summable f)
    (h : ∀ j, j ≠ i → 0 ≤ f j) : f i ≤ tsum f := by
  exact Summable.le_tsum hs i h
