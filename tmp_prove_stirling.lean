import Mathlib
open Real Finset
open scoped BigOperators

lemma sum_log_stirling (N : ℕ) (hN : N ≥ 1) : 
    |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 1 := by
  have h_int_val : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]; ring
  
  -- For n ≥ 1: log n ≤ ∫_n^{n+1} log t dt ≤ log(n+1)
  have h_interval_bound (n : ℕ) (hn : 1 ≤ n) : Real.log (n : ℝ) ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ∧
      ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ Real.log ((n+1 : ℕ) : ℝ) := by
    have h_n_n1 : (n : ℝ) ≤ n+1 := by nlinarith
    have h_cont_log : ContinuousAt Real.log (n : ℝ) := Real.continuousAt_log (by exact_mod_cast (Nat.pos_of_gt (by omega)))
    have h_int_const_n : IntervalIntegrable (λ _ : ℝ => Real.log (n : ℝ)) volume (n : ℝ) (n+1 : ℝ) :=
      intervalIntegrable_const
    have h_int_log : IntervalIntegrable Real.log volume (n : ℝ) (n+1 : ℝ) :=
      (Real.continuousAt_log (fun t => ?_)).intervalIntegrable
    have h_int_const_n1 : IntervalIntegrable (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) volume (n : ℝ) (n+1 : ℝ) :=
      intervalIntegrable_const
    
    have h_log_le : (λ _ : ℝ => Real.log (n : ℝ)) ≤ Real.log := by
      intro t ht
      have ht_pos : 0 < t := by
        have : (n : ℝ) ≤ t := ht
        nlinarith
      exact Real.log_le_log (by exact_mod_cast hn) (by nlinarith)
    have h_log_le' : Real.log ≤ (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) := by
      intro t ht
      have ht_pos : 0 < t := by
        have : (n : ℝ) ≤ t := ht
        nlinarith
      have h_t_n1 : t ≤ (n+1 : ℝ) := ht
      exact Real.log_le_log (by nlinarith) (by nlinarith)
    
    have h_low : Real.log (n : ℝ) ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
      calc
        Real.log (n : ℝ) = ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log (n : ℝ) := by
          simp
        _ ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t :=
          intervalIntegral.integral_mono h_n_n1 h_int_const_n h_int_log h_log_le
    
    have h_high : ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ Real.log ((n+1 : ℕ) : ℝ) := by
      calc
        ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log ((n+1 : ℕ) : ℝ) :=
          intervalIntegral.integral_mono h_n_n1 h_int_log h_int_const_n1 h_log_le'
        _ = Real.log ((n+1 : ℕ) : ℝ) := by simp
    
    exact And.intro h_low h_high
  
  -- Sum from n=1 to N-1
  have h_sum_low : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
    have h_int_low : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
      calc
        ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
          rw [intervalIntegral.integral_add_adjacent_intervals (by
            intro i hi; have hi' : i ≤ N-1 := (Finset.mem_Icc.mp hi).2; exact mod_cast hi')]
          -- This is still complex
          sorry
        _ ≤ ∑ n ∈ Icc 1 (N-1), Real.log ((n+1 : ℕ) : ℝ) :=
          Finset.sum_le_sum (λ n hn => (h_interval_bound n (by
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; exact hn1)).2)
        _ = ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by
          refine Finset.sum_bij (λ n _ => n+1) ?_ ?_ ?_ ?_ ?_ ?_
          · intro n hn; apply Finset.mem_Icc.mpr
            have hn2 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; have hn3 : n ≤ N-1 := (Finset.mem_Icc.mp hn).2
            constructor <;> omega
          · intro n hn; simp
          · intro a ha b hb h; omega
          · intro m hm; have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1; have hm3 : m ≤ N := (Finset.mem_Icc.mp hm).2
            refine ⟨m-1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩; omega
          · rfl
        _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
          have h_eq : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
          rw [h_eq, Finset.sum_union (by simp), Finset.sum_singleton]; simp
    rw [h_int_val] at h_int_low; linarith
  
  have h_sum_high : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 + Real.log (N : ℝ) := by
    have h_int_high : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ ∫ t in (1 : ℝ)..(N : ℝ), Real.log t + Real.log (N : ℝ) := by
      calc
        ∑ n ∈ Icc 1 N, Real.log (n : ℝ) = Real.log (1 : ℝ) + ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by
          have : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
          rw [this, Finset.sum_union (by simp), Finset.sum_singleton]; simp
        _ = ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by simp
        _ = ∑ n ∈ Icc 1 (N-1), Real.log ((n+1 : ℕ) : ℝ) := by
          -- index shift: m = n+1, where m ∈ Icc 2 N
          refine (Finset.sum_bij (λ m _ => m-1) ?_ ?_ ?_ ?_ ?_ ?_).symm
          · intro m hm; apply Finset.mem_Icc.mpr
            have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1; have hm3 : m ≤ N := (Finset.mem_Icc.mp hm).2
            constructor <;> omega
          · intro m hm; simp
          · intro a ha b hb h; omega
          · intro n hn; have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; have hn2 : n ≤ N-1 := (Finset.mem_Icc.mp hn).2
            refine ⟨n+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩; omega
          · rfl
        _ ≤ ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t :=
          Finset.sum_le_sum (λ n hn => (h_interval_bound n (by
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; exact hn1)).2.symm)
        _ = ∫ t in (1 : ℝ)..(N : ℝ), Real.log t := by
          rw [intervalIntegral.integral_add_adjacent_intervals (by
            intro i hi; have hi' : i ≤ N-1 := (Finset.mem_Icc.mp hi).2; exact mod_cast hi')]
          -- This is still complex
          sorry
    rw [h_int_val] at h_int_high; linarith
  
  rcases h_sum_low, h_sum_high with ⟨hlow, hhigh⟩
  rw [abs_le]; constructor <;> linarith
