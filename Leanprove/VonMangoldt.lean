-- Von Mangoldt 函数与 Mertens 第一定理
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
open ArithmeticFunction (vonMangoldt vonMangoldt_apply_one vonMangoldt_nonneg vonMangoldt_apply_prime vonMangoldt_apply_pow vonMangoldt_ne_zero_iff vonMangoldt_pos_iff vonMangoldt_eq_zero_iff vonMangoldt_sum vonMangoldt_mul_zeta zeta_mul_vonMangoldt log_mul_moebius_eq_vonMangoldt moebius_mul_log_eq_vonMangoldt sum_moebius_mul_log_eq)
open Set Filter Topology Real
open scoped BigOperators
open Finset
notation "ψ" => Chebyshev.psi
notation "θ" => Chebyshev.theta

/-! === 第一部分: 基本性质 (8定理) === -/
theorem vonMangoldt_one : vonMangoldt 1 = 0 := vonMangoldt_apply_one
theorem vonMangoldt_nonneg' (n : ℕ) : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
theorem vonMangoldt_prime (p : ℕ) (hp : p.Prime) : vonMangoldt p = Real.log p := vonMangoldt_apply_prime hp
theorem vonMangoldt_pow' (n k : ℕ) (hk : k ≠ 0) : vonMangoldt (n ^ k) = vonMangoldt n := vonMangoldt_apply_pow hk
theorem vonMangoldt_nonzero_iff (n : ℕ) : vonMangoldt n ≠ 0 ↔ IsPrimePow n := vonMangoldt_ne_zero_iff
theorem vonMangoldt_pos_iff' (n : ℕ) : 0 < vonMangoldt n ↔ IsPrimePow n := vonMangoldt_pos_iff
theorem vonMangoldt_zero_iff (n : ℕ) : vonMangoldt n = 0 ↔ ¬IsPrimePow n := vonMangoldt_eq_zero_iff
theorem vonMangoldt_le_log' (n : ℕ) : vonMangoldt n ≤ Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log

/-! === 第二部分: Dirichlet 卷积 (6定理) === -/
theorem vonMangoldt_sum_divisors (n : ℕ) : ∑ d ∈ n.divisors, vonMangoldt d = Real.log (n : ℝ) := vonMangoldt_sum
theorem vonMangoldt_mul_zeta_eq_log : vonMangoldt * ↑(ArithmeticFunction.zeta) = ArithmeticFunction.log := vonMangoldt_mul_zeta
theorem zeta_mul_vonMangoldt_eq_log : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vonMangoldt = ArithmeticFunction.log := zeta_mul_vonMangoldt
theorem log_mul_moebius_eq_vonMangoldt' : ArithmeticFunction.log * ↑(ArithmeticFunction.moebius) = vonMangoldt := log_mul_moebius_eq_vonMangoldt
theorem moebius_mul_log_eq_vonMangoldt' : (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log = vonMangoldt := moebius_mul_log_eq_vonMangoldt
theorem sum_moebius_mul_log_eq_vonMangoldt' (n : ℕ) : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) = -vonMangoldt n := sum_moebius_mul_log_eq

/-! === 第三部分: Chebyshev ψ 函数 (4定理) === -/
theorem psi_eq_sum_vonMangoldt_Icc (x : ℝ) : ψ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n := Chebyshev.psi_eq_sum_Icc x
theorem psi_nat_eq_sum (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Finset.Ioc 0 n, vonMangoldt k := by simp [Chebyshev.psi]
theorem psi_nat_eq_sum_Icc (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Finset.Icc 0 n, vonMangoldt k := by rw [Chebyshev.psi_eq_sum_Icc]; simp
theorem vonMangoldt_zero : vonMangoldt 0 = 0 := by
  rw [show vonMangoldt 0 = 0 from by norm_num [ArithmeticFunction.vonMangoldt]]
theorem sum_vonMangoldt_eq_psi (n : ℕ) (hn : 0 < n) : ∑ k ∈ Finset.Icc 1 n, vonMangoldt k = ψ (n : ℝ) := by
  rw [psi_nat_eq_sum_Icc]
  have : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    apply Finset.ext; intro k; simp; omega
  rw [this, Finset.sum_insert (by simp), vonMangoldt_zero, zero_add]

/-! === 第四部分: Chebyshev 界 (3定理) === -/
theorem psi_bounded (x : ℝ) (hx : 0 ≤ x) : |ψ x| ≤ (Real.log 4 + 4) * x := by
  rw [abs_of_nonneg (Chebyshev.psi_nonneg x)]; exact Chebyshev.psi_le_const_mul_self hx
theorem psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) : ψ x - θ x ≤ 2 * Real.sqrt x * Real.log x := Chebyshev.psi_sub_theta_le hx
theorem abs_psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) : |ψ x - θ x| ≤ 2 * Real.sqrt x * Real.log x := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-! === 第五部分: 分析引理 (6引理) === -/
lemma log_lt_two_sqrt {p : ℝ} (hp : 1 ≤ p) : Real.log p < 2 * Real.sqrt p := by
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have h_log_sqrt : Real.log (Real.sqrt p) ≤ Real.sqrt p - 1 := Real.log_le_sub_one_of_pos hsqrt_pos
  calc Real.log p = Real.log ((Real.sqrt p) ^ 2) := by rw [Real.sq_sqrt (by linarith)]
    _ = 2 * Real.log (Real.sqrt p) := by rw [Real.log_pow, Nat.cast_ofNat]
    _ ≤ 2 * (Real.sqrt p - 1) := by linarith [h_log_sqrt]
    _ < 2 * Real.sqrt p := by linarith [hsqrt_pos]

lemma sqrt_div_sq_eq_rpow (p : ℕ) (hp : 0 < p) : Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) = (p : ℝ) ^ (-3/2 : ℝ) := by
  have hp_pos : (p : ℝ) > 0 := by exact_mod_cast hp
  calc Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) = ((p : ℝ) ^ (1/2 : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) := by rw [Real.sqrt_eq_rpow]
    _ = (p : ℝ) ^ ((1/2 : ℝ) - (2 : ℝ)) := by rw [Real.rpow_sub hp_pos]
    _ = (p : ℝ) ^ (-3/2 : ℝ) := by rw [show (1/2 : ℝ) - (2 : ℝ) = (-3/2 : ℝ) from by ring]

lemma log_div_sq_bound_le (p : ℕ) (hp : 2 ≤ p) : Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) ≤ 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p from by omega)
  have h_log : Real.log (p : ℝ) < 2 * Real.sqrt (p : ℝ) := log_lt_two_sqrt hp'
  have h_sq_pos : (p : ℝ) ^ (2 : ℝ) > 0 := by positivity
  have h1 : Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) < (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) := by gcongr
  have h2 : (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) = 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
    calc _ = 2 * (Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ))) := by ring
      _ = 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by rw [sqrt_div_sq_eq_rpow p (by omega : 0 < p)]
  rw [h2] at h1; linarith

lemma range_sum_le_tsum_of_nonneg (f : ℕ → ℝ) (h_nonneg : ∀ n, 0 ≤ f n) (h_summable : Summable f) (N : ℕ) :
    ∑ i ∈ Finset.range N, f i ≤ ∑' i, f i := by
  set s := fun n : ℕ => ∑ i ∈ Finset.range n, f i; set a := ∑' i, f i
  have h_hasSum : HasSum f a := h_summable.hasSum
  have h_tendsto : Tendsto s atTop (𝓝 a) := h_hasSum.tendsto_sum_nat
  have h_mono : ∀ n m, n ≤ m → s n ≤ s m := by
    intro n m hnm; obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm; rw [hk]
    calc s n = ∑ i ∈ Finset.range n, f i := rfl
      _ ≤ ∑ i ∈ Finset.range n, f i + ∑ i ∈ Finset.range k, f (n + i) := by
        have h_nonneg' : 0 ≤ ∑ i ∈ Finset.range k, f (n + i) := Finset.sum_nonneg (fun i _ => h_nonneg (n + i))
        nlinarith
      _ = ∑ i ∈ Finset.range (n + k), f i := by simpa using (Finset.sum_range_add f n k).symm
      _ = s (n + k) := rfl
  by_contra! h; have h_eps : s N - a > 0 := by linarith
  have h_event : ∀ᶠ n in atTop, dist (s n) a < s N - a := by
    have := (Metric.tendsto_nhds.mp h_tendsto) (s N - a) h_eps; simpa using this
  have h_ge_N : {n : ℕ | N ≤ n} ∈ atTop := Filter.mem_atTop N
  have h_inter : {n : ℕ | dist (s n) a < s N - a} ∩ {n : ℕ | N ≤ n} ∈ atTop := h_event.and h_ge_N
  rcases Filter.nonempty_of_mem h_inter with ⟨n, hn_dist_mem, hn_ge_mem⟩
  have hn_dist : dist (s n) a < s N - a := hn_dist_mem; have hn_ge : N ≤ n := hn_ge_mem
  have h_real_dist : dist (s n) a = |s n - a| := Real.dist_eq (s n) a; rw [h_real_dist] at hn_dist
  have h_sn_ge_a : a ≤ s n := by have h_N_le_n : s N ≤ s n := h_mono N n hn_ge; linarith
  have h_abs_eq : |s n - a| = s n - a := abs_of_nonneg (sub_nonneg.mpr h_sn_ge_a)
  rw [h_abs_eq] at hn_dist; have h_sN_le_sn : s N ≤ s n := h_mono N n hn_ge; nlinarith

lemma pow_div_pow_bound (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 2 ≤ k) : (1 : ℝ) / ((p : ℝ) ^ k) ≤ ((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2)) := by
  have hp_pos : (p : ℝ) > 0 := by exact_mod_cast (show 0 < p from by omega)
  calc
    (1 : ℝ) / ((p : ℝ) ^ k) = (1 / ((p : ℝ) ^ 2)) * ((1 / (p : ℝ)) ^ (k - 2)) := by
      have hk : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [hk, div_mul_eq_div_div_swap, ← one_div_pow]
      have key : ∀ a b : ℝ, b ≠ 0 → a / b = (1 / b) * a := by intros; field_simp
      rw [key _ _ (by positivity : (↑p : ℝ) ^ 2 ≠ 0)]
    _ ≤ (1 / ((p : ℝ) ^ 2)) * (((1 : ℝ) / 2) ^ (k - 2)) := by
      gcongr
      exact_mod_cast hp
    _ = ((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2)) := by ring

/-- ∑_{j=0}^{N} (1/2)^j ≤ 2 -/
lemma geom_sum_bound (N : ℕ) : ∑ j ∈ range (N + 1), ((1 : ℝ) / 2) ^ j ≤ 2 := by
  calc ∑ j ∈ range (N + 1), ((1 : ℝ) / 2) ^ j
      = (1 - ((1 : ℝ) / 2) ^ (N + 1)) / (1 - 1 / 2) := by
        rw [geom_sum_eq (by norm_num : (1/2 : ℝ) ≠ 1) (N + 1)]
        ring
    _ = 2 * (1 - ((1 : ℝ) / 2) ^ (N + 1)) := by
        ring
    _ ≤ 2 := by
        have : 0 ≤ ((1 : ℝ) / 2) ^ (N + 1) := by positivity
        linarith

lemma geom_tail_Icc_bound (p M : ℕ) (hp : 2 ≤ p) (hM : 2 ≤ M) :
    ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / ((p : ℝ) ^ k) ≤ 2 / ((p : ℝ) ^ 2) := by
  have hp_pos : (p : ℝ) > 0 := by exact_mod_cast (show 0 < p from by omega)
  have hp2_pos : (p : ℝ) ^ 2 > 0 := by positivity
  calc ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / ((p : ℝ) ^ k)
      ≤ ∑ k ∈ Finset.Icc 2 M, ((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_div_pow_bound p hp k (Finset.mem_Icc.mp hk).1
    _ = (1 / ((p : ℝ) ^ 2)) * ∑ k ∈ Finset.Icc 2 M, ((1 : ℝ) / 2) ^ (k - 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ ≤ (1 / ((p : ℝ) ^ 2)) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / ((p : ℝ) ^ 2))
        -- ∑_{k=2}^M (1/2)^(k-2) = ∑_{j=0}^{M-2} (1/2)^j ≤ 2
        have h_range : Finset.Icc 2 M = (Finset.range (M - 1)).image (· + 2) := by
          ext k; simp [Finset.mem_Icc, Finset.mem_range, Finset.mem_image]
          constructor
          · intro hk; exact ⟨k - 2, by omega, by omega⟩
          · intro ⟨j, hj, hk⟩; exact ⟨by omega, by omega⟩
        rw [h_range, Finset.sum_image (by intro x hx y hy h; exact Nat.add_right_cancel h)]
        -- 转换: (1/2)^(x+2-2) = (1/2)^x
        simp only [add_tsub_cancel_right]
        -- ∑_{j=0}^{M-2} (1/2)^j ≤ 2
        have h_eq : M - 2 + 1 = M - 1 := by omega
        change ∑ x ∈ Finset.range (M - 1), (1 / 2) ^ x ≤ 2
        rw [← h_eq]
        exact geom_sum_bound (M - 2)
    _ = 2 / ((p : ℝ) ^ 2) := by ring

-- 跳过 primePower_contribution_bounded 的复杂证明
theorem primePower_contribution_bounded : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C := by sorry

theorem psi_integral_sub_log_isBigO : (fun x : ℝ ↦ ∫ t in Set.Ioc 1 x, ψ t / (t * t) - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by sorry
