import Mathlib
open Complex Real Filter Finset
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
    · subst hn0; simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
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
  have h_sumnorm : Summable (λ n : ℕ => ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖) :=
    summable_norm_inv_nat_cpow s h
  have h_norm_bound : ‖zeta s‖ ≤ ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ :=
    norm_tsum_le_tsum_norm h_sumnorm
  have h_eq_tsum : ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ = 
      ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ)) := by
    refine tsum_congr (λ n => ?_)
    by_cases hn0 : n = 0
    · subst hn0
      have h0 : (0 : ℝ) ^ (s.re : ℝ) = 0 := Real.zero_rpow (by linarith : s.re ≠ 0)
      have h1 : (1 : ℝ) / (0 : ℝ) ^ (s.re : ℝ) = 0 := by simp [h0]
      simp [h0, h1]
    · simp [hn0, norm_nat_cpow n hn0 s]
  calc
    ‖zeta s‖ ≤ ∑' n : ℕ, ‖(if n = 0 then 0 else (1 : ℂ) / nat_cpow n s)‖ := h_norm_bound
    _ = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (s.re : ℝ)) := h_eq_tsum

/-! ### Euler 乘积 -/

/-- 辅助引理: 对任意有限素数集 S, 乘积展开为光滑数和 -/
lemma prod_geo_expand (S : Finset ℕ) (σ : ℝ) (hσ : 1 < σ) :
    ∏ p ∈ S, ((1 : ℝ) - ((p : ℝ) ^ (-σ)))⁻¹ = ∑' n : ℕ, (if (∀ p ∈ Nat.primeFactors n, p ∈ S) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) := by
  induction' S using Finset.induction with q S hq IH
  · -- S = ∅: 乘积 = 1, 求和 = 1 (只有 n=1 满足无素因子的条件)
    have h_condition : ∀ n : ℕ, ((∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0) ↔ n = 1 := by
      intro n; constructor
      · rintro ⟨h, hn0⟩
        by_contra! hx
        have hx' : n ≠ 0 := hn0
        have h_comp : n ≠ 1 := hx
        rcases Nat.exists_prime_and_dvd h_comp with ⟨p, hp_prime, hp_dvd⟩
        have hp_mem : p ∈ Nat.primeFactors n :=
          Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, by omega⟩
        have : p ∈ (∅ : Finset ℕ) := h p hp_mem
        simp at this
      · intro h; subst h; simp
    have h_tsum : ∑' n : ℕ, (if (∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) = 1 := by
      haveI : (SummationFilter.unconditional ℕ).LeAtTop := by infer_instance
      have hf : ∀ n : ℕ, n ∉ ({1} : Finset ℕ) → (if (∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) = 0 := by
        intro n hn
        have hn1 : n ≠ 1 := by intro h; apply hn; simp [h]
        have h_false : ¬((∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0) := by
          rintro ⟨h_cond, hn0⟩
          apply hn1
          exact ((h_condition n).mp ⟨h_cond, hn0⟩)
        simp only [h_false, if_false]
      have h_sum : ∑ n ∈ ({1} : Finset ℕ), (if (∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) = 1 := by
        simp
      calc
        ∑' n : ℕ, (if (∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) = 
            ∑ n ∈ ({1} : Finset ℕ), (if (∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) :=
          tsum_eq_sum hf
        _ = 1 := h_sum
    simpa [eq_comm] using h_tsum
  · -- S = T ∪ {q} 其中 q ∉ T
    rw [Finset.prod_insert hq, IH]
    -- 需要证明: (1 - q^{-σ})⁻¹ * ∑_{n smooth w.r.t. T} n^{-σ} = ∑_{m smooth w.r.t. T ∪ {q}} m^{-σ}
    sorry

/-- 有限 Euler 乘积 ≥ 部分和: ∏_{p ≤ X} (1 - p^{-σ})⁻¹ ≥ ∑_{n=1}^{X} n^{-σ} -/
lemma euler_product_partial_ge (σ : ℝ) (hσ : 1 < σ) (X : ℕ) (hX : X ≥ 1) :
    ∏ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 - ((p : ℝ) ^ (-σ)))⁻¹ ≥ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / ((n : ℝ) ^ σ) := by
  have h_eq := prod_geo_expand ((Finset.Icc 2 X).filter Nat.Prime) σ hσ
  -- 右侧是 ∑_{n smooth} n^{-σ}
  -- 对每个 n ≤ X, 所有素因子 ≤ n ≤ X, 所以 n 是 smooth 的
  have h_mem : ∀ n : ℕ, n ≥ 1 → n ≤ X → (∀ p ∈ Nat.primeFactors n, p ∈ (Finset.Icc 2 X).filter Nat.Prime) := by
    intro n hn1 hnX
    intro p hp
    rcases Nat.mem_primeFactors.mp hp with ⟨hp_prime, hp_dvd, hp_pos⟩
    have hp_le_n : p ≤ n := Nat.le_of_dvd hn1 hp_dvd
    have hp_ge_2 : 2 ≤ p := Nat.Prime.two_le hp_prime
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hp_le_n hnX⟩, hp_prime⟩
  sorry

/-- ζ(σ) = lim_{X→∞} ∏_{p ≤ X} (1 - p^{-σ})⁻¹ (Euler 乘积) -/
lemma euler_product_zeta (σ : ℝ) (hσ : 1 < σ) : 
    Filter.Tendsto (λ (X : ℕ) => ∏ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 - ((p : ℝ) ^ (-σ)))⁻¹) Filter.atTop (nhds (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ σ))) := by
  sorry
