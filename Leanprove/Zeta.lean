import Mathlib
open Complex Real Filter
open scoped BigOperators

noncomputable section

/-- 自然数 n 的复指数: n^s = exp(s·log n) -/
def nat_cpow (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ s

lemma nat_cpow_eq_exp_log_mul (n : ℕ) (hn : n ≠ 0) (s : ℂ) : nat_cpow n s = cexp ((Real.log (n : ℝ) : ℂ) * s) := by
  dsimp [nat_cpow]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn : (n : ℂ) ≠ 0) s]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n))).symm
  rw [hlog]

lemma norm_nat_cpow (n : ℕ) (hn : n ≠ 0) (s : ℂ) : ‖nat_cpow n s‖ = ((n : ℝ) ^ (s.re : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hlog_eq : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n))).symm
  have h_re : ((Real.log (n : ℝ) : ℂ) * s).re = Real.log (n : ℝ) * s.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    ‖nat_cpow n s‖ = ‖cexp ((Real.log (n : ℝ) : ℂ) * s)‖ := by rw [nat_cpow_eq_exp_log_mul n hn s]
    _ = Real.exp (((Real.log (n : ℝ) : ℂ) * s).re) := Complex.norm_exp ((Real.log (n : ℝ) : ℂ) * s)
    _ = Real.exp (Real.log (n : ℝ) * s.re) := by rw [h_re]
    _ = (n : ℝ) ^ (s.re : ℝ) := by rw [Real.rpow_def_of_pos hnpos]

lemma summable_norm_inv_nat_cpow (s : ℂ) (h : 1 < s.re) : Summable (λ n : ℕ => ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖) := by
  have h_nonneg : ∀ n : ℕ, 0 ≤ ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ := by
    intro n; positivity
  have hsum : Summable (λ n : ℕ => ((n : ℝ) ^ (-(s.re : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h_bound : ∀ n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ ≤ ((n : ℝ) ^ (-(s.re : ℝ))) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0; simp
      have : -s.re ≠ 0 := by linarith
      simp [Real.zero_rpow this]
    · have h_val : ‖(1 : ℂ) / nat_cpow n s‖ = ((n : ℝ) ^ (-(s.re : ℝ))) := by
        calc
          ‖(1 : ℂ) / nat_cpow n s‖ = ‖(1 : ℂ)‖ / ‖nat_cpow n s‖ := by rw [norm_div]
          _ = 1 / ‖nat_cpow n s‖ := by simp
          _ = 1 / ((n : ℝ) ^ (s.re : ℝ)) := by rw [norm_nat_cpow n hn0 s]
          _ = ((n : ℝ) ^ (-(s.re : ℝ))) := by
            rw [Real.rpow_neg (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n))]
            simp
      have h_norm : ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ = ‖(1 : ℂ) / nat_cpow n s‖ := by
        simp [hn0]
      rw [h_norm, h_val]
  have h_nonneg' : ∀ n : ℕ, 0 ≤ ‖(1 : ℂ) / nat_cpow n s‖ := by
    intro n; positivity
  refine Summable.of_nonneg_of_le h_nonneg h_bound hsum

/-- ζ(s) = ∑_{n=1}^{∞} 1/n^s, 定义域 Re(s) > 1 -/
def zeta (s : ℂ) : ℂ := ∑' n : ℕ, (if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)

/-- ζ(s) 绝对收敛: Re(s) > 1 时 ∑ 1/|n^s| 收敛 -/
lemma zeta_abs_convergent (s : ℂ) (h : 1 < s.re) : Summable (λ n : ℕ => (if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)) :=
  Summable.of_norm (summable_norm_inv_nat_cpow s h)
