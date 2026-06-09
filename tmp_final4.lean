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
  have h_int_const : IntervalIntegrable (λ _ : ℝ => Real.log (n : ℝ)) volume (n : ℝ) (n+1 : ℝ) := intervalIntegrable_const
  have h_int_log : IntervalIntegrable Real.log volume (n : ℝ) (n+1 : ℝ) :=
    (Real.continuousOn_log.mono h_uicc).intervalIntegrable
  have h_int_n1 : IntervalIntegrable (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) volume (n : ℝ) (n+1 : ℝ) := intervalIntegrable_const
  have h_log_le : (λ _ : ℝ => Real.log (n : ℝ)) ≤ Real.log := by
    intro t ht; have htpos : 0 < t := by nlinarith; exact Real.log_le_log (by exact_mod_cast hn) (by nlinarith)
  have h_log_le' : Real.log ≤ (λ _ : ℝ => Real.log ((n+1 : ℕ) : ℝ)) := by
    intro t ht; have htpos : 0 < t := by nlinarith; exact Real.log_le_log htpos (by nlinarith)
  constructor
  · calc
      Real.log (n : ℝ) = ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log (n : ℝ) := by simp
      _ ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := intervalIntegral.integral_mono h_n_n1 h_int_const h_int_log h_log_le
  · calc
      ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log ((n+1 : ℕ) : ℝ) :=
        intervalIntegral.integral_mono h_n_n1 h_int_log h_int_n1 h_log_le'
      _ = Real.log ((n+1 : ℕ) : ℝ) := by simp

lemma int_splitsum (N : ℕ) (hN : N ≥ 1) : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := by
  induction' N using Nat.strong_induction_on with N IH
  rcases N with (h | N)
  · omega
  · rename_i N
    rcases N with (h | K)
    · -- N = 1 case
      simp
    · -- N = K+2, where K ≥ 0, K.succ.succ = K+2 ≥ 2
      rename_i K
      have hKpos : 0 ≤ K := Nat.zero_le _
      have hNpos : 1 ≤ K.succ.succ := by omega
      have hKN : K.succ ≤ K.succ.succ := by omega
      have h_int_add : ∫ t in (1 : ℝ)..(K.succ.succ : ℝ), Real.log t =
          ∫ t in (1 : ℝ)..(K.succ : ℝ), Real.log t + ∫ t in (K.succ : ℝ)..(K.succ.succ : ℝ), Real.log t := by
        rw [intervalIntegral.integral_add_adjacent_intervals ?_ ?_]
        · have h1 : IntervalIntegrable Real.log volume (1 : ℝ) (K.succ : ℝ) :=
            (Real.continuousOn_log.mono (λ x hx => ?_)).intervalIntegrable
          sorry
        · have h2 : IntervalIntegrable Real.log volume (K.succ : ℝ) (K.succ.succ : ℝ) :=
            (Real.continuousOn_log.mono (λ x hx => ?_)).intervalIntegrable
          sorry
      sorry

lemma sum_log_stirling (N : ℕ) (hN : N ≥ 1) : 
    |∑ n ∈ Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ))| ≤ Real.log (N : ℝ) + 1 := by
  have h_int_val : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]; ring
  
  have h_low : ∑ n ∈ Icc 1 (N-1), Real.log (n : ℝ) ≤ ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t :=
    Finset.sum_le_sum (λ n hn => (log_interval_ineq n (by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; exact hn1)).1)
  
  have h_split : ∫ t in (1 : ℝ)..(N : ℝ), Real.log t = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t :=
    int_splitsum N hN
  
  have h_sum_high : ∑ n ∈ Icc 1 N, Real.log (n : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 + Real.log (N : ℝ) := by
    calc
      ∑ n ∈ Icc 1 N, Real.log (n : ℝ) = (∑ n ∈ Icc 1 (N-1), Real.log (n : ℝ)) + Real.log (N : ℝ) := by
        rcases N with (h | N)
        · omega
        · simp [Finset.Icc_succ_singleton, add_comm]
        sorry
      _ ≤ (∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t) + Real.log (N : ℝ) := by
        nlinarith
      _ = (∫ t in (1 : ℝ)..(N : ℝ), Real.log t) + Real.log (N : ℝ) := by rw [h_split]
      _ = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 + Real.log (N : ℝ) := by rw [h_int_val]
  
  have h_sum_low : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
    calc
      (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 = ∫ t in (1 : ℝ)..(N : ℝ), Real.log t := by rw [h_int_val]
      _ = ∑ n ∈ Icc 1 (N-1), ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t := h_split
      _ ≤ ∑ n ∈ Icc 1 (N-1), Real.log ((n+1 : ℕ) : ℝ) :=
        Finset.sum_le_sum (λ n hn => (log_interval_ineq n (by
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1; exact hn1)).2)
      _ = ∑ n ∈ Icc 2 N, Real.log (n : ℝ) := by
        refine Finset.sum_bij (λ n _ => n+1) ?_ ?_ ?_ ?_ ?_ ?_
        · intro n hn; rcases Finset.mem_Icc.mp hn with ⟨hn1, hn2⟩
          apply Finset.mem_Icc.mpr; constructor <;> omega
        · intro n hn; simp
        · intro a ha b hb h; omega
        · intro m hm; rcases Finset.mem_Icc.mp hm with ⟨hm2, hmN⟩
          refine ⟨m-1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩; omega
        · rfl
      _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
        have h_eq : Icc 1 N = {1} ∪ Icc 2 N := by ext n; simp; omega
        rw [h_eq, Finset.sum_union (by simp), Finset.sum_singleton]; simp
  
  rw [abs_le]; constructor <;> nlinarith
