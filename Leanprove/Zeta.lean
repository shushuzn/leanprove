import Mathlib
open Complex Real Filter Topology Finset
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

/-- 辅助引理: 对任意有限集 S (元素 ≥ 2), 乘积展开为光滑数和 -/
lemma prod_geo_expand (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (σ : ℝ) (hσ : 1 < σ) :
    ∏ p ∈ S, ((1 : ℝ) - ((p : ℝ) ^ (-σ)))⁻¹ = ∑' n : ℕ, (if (∀ p ∈ Nat.primeFactors n, p ∈ S) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0) := by
  induction' S using Finset.induction with q S hq IH
  · -- S = ∅: 乘积 = 1, 求和 = 1
    have h_condition : ∀ n : ℕ, ((∀ p ∈ Nat.primeFactors n, p ∈ (∅ : Finset ℕ)) ∧ n ≠ 0) ↔ n = 1 := by
      intro n; constructor
      · rintro ⟨h, hn0⟩
        by_contra! hx
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
    have hq_ge_2 : 2 ≤ q := hS q (Finset.mem_insert_self q S)
    have hS_ge_2 : ∀ p ∈ S, 2 ≤ p := λ p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hq, IH S hS_ge_2 σ hσ]
    
    let f_T (n : ℕ) : ℝ := if (∀ p ∈ Nat.primeFactors n, p ∈ S) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0
    let f_Tq (n : ℕ) : ℝ := if (∀ p ∈ Nat.primeFactors n, p ∈ (insert q S)) ∧ n ≠ 0 then (1 : ℝ) / ((n : ℝ) ^ σ) else 0
    
    -- 需要证明: (1 - q^{-σ})⁻¹ * (∑' n, f_T n) = (∑' n, f_Tq n)
    have h_q_pow : 0 < (q : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast (Nat.one_le_of_lt (by omega))) _
    have h_norm : |(q : ℝ) ^ (-σ)| < 1 := by
      have h_pow_lt_one : (q : ℝ) ^ (-σ) < 1 := by
        refine (Real.rpow_lt_rpow_of_exponent_lt ?_ (by linarith)).trans_eq ?_
        · exact_mod_cast (show 1 < q from by omega)
        · simp
      rw [abs_of_pos h_q_pow]
      exact h_pow_lt_one
    
    have h_geo_hasSum : HasSum (λ k : ℕ => ((q : ℝ) ^ (-σ)) ^ k) ((1 : ℝ) - ((q : ℝ) ^ (-σ)))⁻¹ := by
      simpa [Real.one_div] using hasSum_geometric_of_norm_lt_one h_norm
    have h_geo_summable : Summable (λ k : ℕ => ((q : ℝ) ^ (-σ)) ^ k) := h_geo_hasSum.summable
    
    have h_fT_summable : Summable f_T := by
      -- f_T(n) ≤ n^{-σ}, 且 ∑ n^{-σ} 收敛
      have h_bound : ∀ n : ℕ, f_T n ≤ (1 : ℝ) / ((n : ℝ) ^ σ) := by
        intro n; dsimp [f_T]; split <;> try positivity
        · split <;> positivity
        · positivity
      have h_summable_ref : Summable (λ n : ℕ => (1 : ℝ) / ((n : ℝ) ^ σ)) := by
        have : Summable (λ n : ℕ => ((n : ℝ) ^ (-σ : ℝ))) :=
          Real.summable_nat_rpow.mpr (by linarith)
        have h_eq : (λ n : ℕ => (1 : ℝ) / ((n : ℝ) ^ σ)) = (λ n : ℕ => ((n : ℝ) ^ (-σ : ℝ))) := by
          ext n; simp [Real.rpow_neg (by exact_mod_cast (Nat.zero_le n) : 0 ≤ (n : ℝ))]
        rw [h_eq]; exact this
      have h_nonneg : ∀ n : ℕ, 0 ≤ f_T n := by
        intro n; dsimp [f_T]; split <;> try positivity
        split <;> positivity
      exact Summable.of_nonneg_of_le h_nonneg h_bound h_summable_ref
    
    -- 多项展开: (∑ q^{-kσ})·(∑ f_T(m)) = ∑_{(k,m)} (q^k)^{-σ}·f_T(m)
    -- 用 tsum_mul_tsum 处理乘积
    have h_prod : ((1 : ℝ) - ((q : ℝ) ^ (-σ)))⁻¹ * (∑' n : ℕ, f_T n) = ∑' (x : ℕ × ℕ), (((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2) := by
      calc
        ((1 : ℝ) - ((q : ℝ) ^ (-σ)))⁻¹ * (∑' n : ℕ, f_T n) = 
            (∑' k : ℕ, ((q : ℝ) ^ (-σ)) ^ k) * (∑' n : ℕ, f_T n) := by rw [h_geo_hasSum.tsum_eq]
        _ = ∑' (x : ℕ × ℕ), (((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2) := 
          tsum_mul_tsum h_geo_summable h_fT_summable
    
    -- 双射: (k,m) → n = q^k·m 把求和重写为 f_Tq(n)
    have h_bij : ∑' (x : ℕ × ℕ), (((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2) = ∑' n : ℕ, f_Tq n := by
      have h_nonneg_prod : ∀ x : ℕ × ℕ, 0 ≤ ((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2 := by
        intro x; positivity
      -- 用 tsum_bij 重排
      refine (tsum_bij (λ (x : ℕ × ℕ) => q ^ x.1 * x.2) ?_ ?_ ?_ ?_ ?_).symm
      · intro x hx
        dsimp [f_Tq]
        have hq_factor : ∀ p ∈ Nat.primeFactors (q ^ x.1 * x.2), p ∈ insert q S := by
          intro p hp
          rcases Nat.mem_primeFactors.mp hp with ⟨hp_prime, hp_dvd, hp_pos⟩
          -- p ∣ q^x.1 * x.2, 所以 p ∣ q^x.1 或 p ∣ x.2
          rcases hp_prime.dvd_mul.mp hp_dvd with (h | h)
          · -- p ∣ q^k, 所以 p = q
            have h_p_eq_q : p = q := hp_prime.eq_of_dvd_dvd (by exact Nat.prime_of_mem_primeFactors hp) h
            simp [h_p_eq_q]
          · -- p ∣ x.2, 由 f_T 条件 p ∈ S
            have hx_mem : ∀ p ∈ Nat.primeFactors x.2, p ∈ S := by
              -- 从 f_T x.2 ≠ 0 可推出
              have : f_T x.2 ≠ 0 := by
                intro hzero
                have : ((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2 = 0 := by simp [hzero]
                -- 但 x 在求和域中, 这个乘积 > 0...
                sorry
              sorry
            sorry
        sorry
      · intro x hx; simp
      · intro x hx y hy h; ... -- 单射
      · intro n hn; ... -- 满射
      · rfl
    
    calc
      ((1 : ℝ) - ((q : ℝ) ^ (-σ)))⁻¹ * (∑' n : ℕ, f_T n) = ∑' (x : ℕ × ℕ), (((q : ℝ) ^ (-σ)) ^ x.1 * f_T x.2) := h_prod
      _ = ∑' n : ℕ, f_Tq n := h_bij
