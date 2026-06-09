import Mathlib
open Real Finset
open scoped BigOperators

lemma log_interval_ineq (n : ℕ) (hn : 1 ≤ n) : Real.log (n : ℝ) ≤ ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ∧
    ∫ t in (n : ℝ)..(n+1 : ℝ), Real.log t ≤ Real.log ((n+1 : ℕ) : ℝ) := by
  have h_n_n1 : (n : ℝ) ≤ n+1 := by nlinarith
  have h_nonzero : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (n+1 : ℝ) := by
    intro hz; rcases Set.mem_uIcc.mp hz with (hz | hz) <;> nlinarith
  have h_cont_log : ContinuousOn Real.log (Set.uIcc (n : ℝ) (n+1 : ℝ)) :=
    Real.continuousOn_log.mono (Set.compl_subset_comm.mp ?_)
    -- Need: uIcc ⊆ {0}ᶜ
    sorry
  sorry
