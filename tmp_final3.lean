import Mathlib
open Real Finset Set
open scoped BigOperators

lemma log_interval_ineq (n : ℕ) (hn : 1 ≤ n) : Real.log (n : ℝ) ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ∧
    ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ Real.log ((n+1 : ℕ) : ℝ) := by
  have h_n_n1 : (n : ℝ) ≤ n+1 := by nlinarith
  have h_uicc : Set.uIcc (n : ℝ) (n+1 : ℝ) ⊆ {0}ᶜ := by
    intro x hx; rcases Set.mem_uIcc.mp hx with (hx' | hx')
    · have : (1 : ℝ) ≤ x := by nlinarith; nlinarith
    · have : (1 : ℝ) ≤ x := by nlinarith; nlinarith
  have h_int_const : IntervalIntegrable (λ _ : ℝ => Real.log (n : ℝ)) volume (n : ℝ) (n+1 : ℝ) :=
    intervalIntegrable_const
  have h_int_log : IntervalIntegrable Real.log volume (n : ℝ) (n+1 : ℝ) :=
    (Real.continuousOn_log.mono h_uicc).intervalIntegrable
  have h_int_n1 : IntervalIntegrable (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) volume (n : ℝ) (n+1 : ℝ) :=
    intervalIntegrable_const
  have h_log_le : (λ _ : ℝ => Real.log (n : ℝ)) ≤ Real.log := by
    intro t ht; have htpos : 0 < t := by
      have : (n : ℝ) ≤ t := ht; nlinarith
    exact Real.log_le_log (by exact_mod_cast hn) (by nlinarith)
  have h_log_le' : Real.log ≤ (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) := by
    intro t ht; have htpos : 0 < t := by
      have : (n : ℝ) ≤ t := ht; nlinarith
    exact Real.log_le_log htpos (by nlinarith)
  constructor
  · calc
      Real.log (n : ℝ) = ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log (n : ℝ) := by simp
      _ ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t :=
        intervalIntegral.integral_mono h_n_n1 h_int_const h_int_log h_log_le
  · calc
      ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log ((n+1 : ℕ) : ℝ) :=
        intervalIntegral.integral_mono h_n_n1 h_int_log h_int_n1 h_log_le'
      _ = Real.log ((n+1 : ℕ) : ℝ) := by simp

lemma sum_log_stirling (N : ℕ) (hN : N ≥ 1) : 
    |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 1 := by
  have h_int_val : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]; ring
  
  -- Split ∫_1^N = ∑_{n=1}^{N-1} ∫_n^{n+1}
  have h_int_split : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
    induction' N with k ih
    · simp
    · rcases eq_or_lt_of_le (Nat.succ_le_succ (Nat.zero_le _)) with (h | h)
      · subst h; simp
      · have hk : 1 ≤ k := by
          rcases k with (h | h)
          · exfalso; omega
          · omega
        have h_last : ∫ t in (k.succ : ℝ)..(k.succ.succ : ℝ), Real.log t = 
            ∫ t in (k.succ : ℝ)..(k.succ.succ : ℝ), Real.log t := rfl
        sorry
    sorry
  
  sorry
