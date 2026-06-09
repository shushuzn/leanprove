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
    calc
      ((Real.log (n : ℝ) : ℂ) * s).re = ((Real.log (n : ℝ) : ℂ).re * s.re - (Real.log (n : ℝ) : ℂ).im * s.im) := rfl
      _ = Real.log (n : ℝ) * s.re - (0 : ℝ) * s.im := by rw [Complex.ofReal_re, Complex.ofReal_im]
      _ = Real.log (n : ℝ) * s.re := by ring
  calc
    ‖nat_cpow n s‖ = ‖cexp ((Real.log (n : ℝ) : ℂ) * s)‖ := by rw [nat_cpow_eq_exp_log_mul n hn s]
    _ = Real.exp (((Real.log (n : ℝ) : ℂ) * s).re) := Complex.norm_exp ((Real.log (n : ℝ) : ℂ) * s)
    _ = Real.exp (Real.log (n : ℝ) * s.re) := by rw [h_re]
    _ = (n : ℝ) ^ (s.re : ℝ) := by rw [Real.rpow_def_of_pos hnpos]

lemma summable_norm_inv_nat_cpow (s : ℂ) (h : 1 < s.re) : Summable (λ n : ℕ => ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖) := by
  have hsum : Summable (λ n : ℕ => ((n : ℝ) ^ (-(s.re : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h_nonneg : ∀ n : ℕ, 0 ≤ ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ := by
    intro n; positivity
  have h_bound : ∀ n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ ≤ ((n : ℝ) ^ (-(s.re : ℝ))) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have h0 : (0 : ℝ) ^ (-(s.re : ℝ)) = 0 := Real.zero_rpow (by linarith : -s.re ≠ 0)
      simp [h0]
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
  refine Summable.of_nonneg_of_le h_nonneg h_bound hsum

/-- ζ(s) = ∑_{n=1}^{∞} 1/n^s, 定义域 Re(s) > 1 -/
def zeta (s : ℂ) : ℂ := ∑' n : ℕ, (if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)

/-- ζ(s) 绝对收敛: Re(s) > 1 时 ∑ 1/|n^s| 收敛 -/
lemma zeta_abs_convergent (s : ℂ) (h : 1 < s.re) : Summable (λ n : ℕ => (if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)) :=
  Summable.of_norm (summable_norm_inv_nat_cpow s h)

/-- ζ(s) 的上界: |ζ(s)| ≤ ζ(Re(s)) -/
lemma norm_zeta_le_zeta_real (s : ℂ) (h : 1 < s.re) : ‖zeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ)) := by
  have h_sum : Summable (λ n : ℕ => (if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)) := zeta_abs_convergent s h
  have h_norm_bound : ‖zeta s‖ ≤ ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ := by
    have h_sumnorm : Summable (λ n : ℕ => ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖) :=
      summable_norm_inv_nat_cpow s h
    exact norm_tsum_le_tsum_norm h_sumnorm
  -- 计算 ∑ ‖a_n‖ = ∑ (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ))
  have h_eq_tsum : ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ = 
      ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ)) := by
    refine tsum_congr (λ n => ?_)
    by_cases hn0 : n = 0
    · subst hn0
      have h0 : (0 : ℝ) ^ (s.re : ℝ) = 0 := by
        have : s.re ≠ 0 := by linarith
        simp [this]
      simp [h0]
    · simp [hn0, norm_div, norm_nat_cpow n hn0 s]
  calc
    ‖zeta s‖ ≤ ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ := h_norm_bound
    _ = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ)) := h_eq_tsum
