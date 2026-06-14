/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- Von Mangoldt 函数与 Mertens 第一定理
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SumIntegralComparisons
import Leanprove.Chebyshev
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

lemma log_div_sq_bound_le (p : ℕ) (hp : 2 ≤ p) : Real.log (p : ℝ) / ((p : ℝ) ^ 2) ≤ 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p from by omega)
  have h_log : Real.log (p : ℝ) < 2 * Real.sqrt (p : ℝ) := log_lt_two_sqrt hp'
  have h_sq_pos : (p : ℝ) ^ 2 > 0 := by positivity
  have h1 : Real.log (p : ℝ) / ((p : ℝ) ^ 2) < (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ 2) := by gcongr
  have h2 : (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ 2) = 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
    have h2a : (p : ℝ) ^ 2 = (p : ℝ) ^ (2 : ℝ) := by
      rw [show (p : ℝ) ^ 2 = (p : ℝ) ^ (2 : ℝ) from (Real.rpow_natCast _ _).symm]
    calc (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ 2)
        = (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) := by rw [h2a]
      _ = 2 * (Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ))) := by ring
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


-- 辅助引理: Λ(n)/n ≥ 0
lemma vm_nonneg (n : ℕ) : 0 ≤ (vonMangoldt n : ℝ) / (n : ℝ) := by
  apply div_nonneg
  · exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  · exact_mod_cast (show 0 ≤ n from by omega)

-- 辅助引理: Λ(n)/n ≤ 1（n ≥ 2）
lemma vm_le_one {n : ℕ} (hn : 2 ≤ n) : (vonMangoldt n : ℝ) / (n : ℝ) ≤ 1 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
  have h_vm := (ArithmeticFunction.vonMangoldt_le_log : (vonMangoldt n : ℝ) ≤ Real.log (n : ℝ))
  have h_log := Real.log_le_self (by linarith : (0 : ℝ) ≤ ↑n)
  have h_bound : (vonMangoldt n : ℝ) ≤ (n : ℝ) := le_trans h_vm h_log
  exact (div_le_one hn_pos).mpr h_bound

-- primePower 贡献有界: 非素数项 (素数幂 p^k, k≥2) 的总贡献有界
-- 证明策略: 双重求和法. 定义 H(m,j) = if m prime then (log m)/(m:ℝ)^(j+2) else 0,
-- 证明 Summable H (通过 summable_prod_of_nonneg), 然后用注入 p^{j+2} 控制部分和.

noncomputable section

/-- 双重求和比较函数: H(m,j) = (log m) / m^(j+2) 若 m 是素数, 否则 0 -/
def Hpp (mj : ℕ × ℕ) : ℝ :=
  if Nat.Prime mj.1 then Real.log (mj.1 : ℝ) / (mj.1 : ℝ) ^ (mj.2 + 2) else 0

@[simp] lemma Hpp_apply (m j : ℕ) : Hpp (m, j) =
    if Nat.Prime m then Real.log (m : ℝ) / (m : ℝ) ^ (j + 2) else 0 := rfl

lemma Hpp_nonneg (mj : ℕ × ℕ) : 0 ≤ Hpp mj := by
  obtain ⟨m, j⟩ := mj
  simp [Hpp_apply]
  split_ifs with hp
  · apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · positivity
  · exact le_rfl

lemma Hpp_inner_summable (m : ℕ) : Summable (fun j : ℕ => Hpp (m, j)) := by
  simp [Hpp_apply]
  split_ifs with hp
  · -- m is prime: ∑_j (log m) / m^(j+2) = (log m)/m² · ∑_j (1/m)^j
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hp.pos
    have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hp.one_lt
    have hratio : (1 : ℝ) / (m : ℝ) < 1 := by
      rw [div_lt_one hm_pos]; exact hm_gt1
    -- Summability of geometric series (extract HasSum from ∃)
    let r := (1 : ℝ) / (m : ℝ)
    obtain ⟨a, ha⟩ := summable_geometric_of_lt_one (by positivity) hratio
    -- ha : HasSum (fun j => r^j) a
    -- Multiply by constant: show HasSum of constant * geometric
    let c := Real.log (m : ℝ) / (m : ℝ) ^ 2
    have h_const : HasSum (fun j => c * r ^ j) (c * a) := by
      -- (fun j => c * r^j) = (fun j => c • r^j) for ℝ
      have heq : (fun j => c * r ^ j) = (fun j => c • r ^ j) := by funext j; simp [smul_eq_mul]
      rw [heq]
      exact ha.const_smul c
    -- Show (log m)/m^(j+2) = c * r^j
    have heq2 : (fun j => Real.log (m : ℝ) / (m : ℝ) ^ (j + 2)) =
        (fun j => c * r ^ j) := by
      funext j
      have hpow : (m : ℝ) ^ (j + 2) = (m : ℝ) ^ 2 * (m : ℝ) ^ j := by rw [pow_add, mul_comm]
      calc Real.log (m : ℝ) / (m : ℝ) ^ (j + 2)
          = Real.log (m : ℝ) / ((m : ℝ) ^ 2 * (m : ℝ) ^ j) := by rw [hpow]
        _ = c * (1 / (m : ℝ) ^ j) := by
            dsimp [c]; field_simp [hm_pos.ne']
        _ = c * r ^ j := by
            congr 1
            simp only [r, one_div]
            exact (inv_pow _ _).symm
    rw [heq2]
    exact ⟨_, h_const⟩
  · exact summable_zero

lemma Hpp_outer_summable : Summable (fun m : ℕ => ∑' j : ℕ, Hpp (m, j)) := by
  -- For prime m: inner tsum = (log m)/m² * m/(m-1) = (log m)/(m*(m-1))
  -- For non-prime m: inner tsum = 0
  -- Bound by 4 * m^{-3/2} and use summable_nat_rpow
  have h_inner_tsum : ∀ m, ∑' j : ℕ, Hpp (m, j) =
      if Nat.Prime m then (Real.log (m : ℝ) / (m : ℝ) ^ 2) * ((m : ℝ) / ((m : ℝ) - 1)) else 0 := by
    intro m
    simp [Hpp_apply]
    split_ifs with hp
    · -- m is prime: compute tsum of geometric series
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hp.pos
      have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hp.one_lt
      have hm_sub1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      let r := (1 : ℝ) / (m : ℝ)
      have hr : r = 1 / (m : ℝ) := rfl
      have hratio : r < 1 := by
        rw [hr, div_lt_one hm_pos]; exact hm_gt1
      -- tsum of geometric series: ∑' r^j = (1-r)⁻¹
      have htsum : ∑' j : ℕ, r ^ j = (1 - r)⁻¹ :=
        tsum_geometric_of_lt_one (by rw [hr]; positivity) hratio
      -- 1 - r = (m-1)/m, so (1-r)⁻¹ = m/(m-1)
      have hinv : (1 - r)⁻¹ = (m : ℝ) / ((m : ℝ) - 1) := by
        have : 1 - r = ((m : ℝ) - 1) / (m : ℝ) := by
          rw [hr]; field_simp [hm_pos.ne']
        rw [this]; field_simp [hm_sub1_pos.ne', hm_pos.ne']
      -- Inner sum = c * tsum = (log m)/m² * m/(m-1)
      have hc : (fun j => Real.log (m : ℝ) / (m : ℝ) ^ (j + 2)) =
          (fun j => (Real.log (m : ℝ) / (m : ℝ) ^ 2) * r ^ j) := by
        funext j
        have hpow : (m : ℝ) ^ (j + 2) = (m : ℝ) ^ 2 * (m : ℝ) ^ j := by rw [pow_add, mul_comm]
        calc Real.log (m : ℝ) / (m : ℝ) ^ (j + 2)
            = Real.log (m : ℝ) / ((m : ℝ) ^ 2 * (m : ℝ) ^ j) := by rw [hpow]
          _ = (Real.log (m : ℝ) / (m : ℝ) ^ 2) * (1 / (m : ℝ) ^ j) := by
              field_simp [hm_pos.ne']
          _ = (Real.log (m : ℝ) / (m : ℝ) ^ 2) * r ^ j := by
              congr 1; simp_rw [hr]; ring
      simp_rw [hc]
      rw [tsum_mul_left, htsum, hinv]
    · simp
  -- Now show summability of (fun m => inner_tsum m)
  -- inner_tsum m ≤ 4 * m^{-3/2} for prime m (0 otherwise)
  have h_bound : ∀ m : ℕ, ∑' j : ℕ, Hpp (m, j) ≤
      if m = 0 ∨ m = 1 then 0 else 4 * ((m : ℝ) ^ (-3/2 : ℝ)) := by
    intro m
    by_cases hp : Nat.Prime m
    · -- prime m
      have hm2 : 2 ≤ m := hp.two_le
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m from by omega)
      have hm_sub1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        linarith
      -- log m / m^2 ≤ 2 * m^{-3/2}
      have h_log_bound : Real.log (m : ℝ) / (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ (-3/2 : ℝ) :=
        log_div_sq_bound_le m hm2
      -- m/(m-1) ≤ 2 for m ≥ 2
      have h_ratio_bound : (m : ℝ) / ((m : ℝ) - 1) ≤ 2 := by
        have : (m : ℝ) ≥ 2 := by exact_mod_cast hm2
        rw [div_le_iff₀ (by linarith)]
        linarith
      -- Combine
      rw [h_inner_tsum, if_pos hp]
      have hm01 : ¬(m = 0 ∨ m = 1) := by omega
      simp [hm01]
      have h_nonneg2 : 0 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
        apply div_nonneg (by positivity) (by linarith)
      have h_prod : (Real.log (m : ℝ) / (m : ℝ) ^ 2) * ((m : ℝ) / ((m : ℝ) - 1))
          ≤ (2 * (m : ℝ) ^ (-3/2 : ℝ)) * 2 := by
        have h_rpow_nonneg : 0 ≤ (2 : ℝ) * (m : ℝ) ^ (-3/2 : ℝ) := by positivity
        exact mul_le_mul h_log_bound h_ratio_bound h_nonneg2 h_rpow_nonneg
      have h_final : (2 * (m : ℝ) ^ (-3/2 : ℝ)) * 2 = 4 * (m : ℝ) ^ (-3/2 : ℝ) := by
        ring_nf
      exact h_prod.trans (le_of_eq h_final)
    · -- non-prime m: inner tsum = 0
      rw [h_inner_tsum, if_neg hp]
      by_cases h01 : m = 0 ∨ m = 1
      · simp [h01]
      · simp [h01]
        have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
        have h_rpow_pos : (0 : ℝ) < (m : ℝ) ^ (-3/2 : ℝ) := Real.rpow_pos_of_pos hm_pos _
        linarith
  -- Use comparison: 0 ≤ inner_tsum ≤ 4*m^{-3/2}, and ∑ 4*m^{-3/2} is summable
  have h_summable_bound : Summable (fun m : ℕ =>
      if m = 0 ∨ m = 1 then (0 : ℝ) else 4 * ((m : ℝ) ^ (-3/2 : ℝ))) := by
    have h_rpow_sum : Summable (fun m : ℕ => (m : ℝ) ^ (-3/2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)
    have h4_sum : Summable (fun m : ℕ => 4 * (m : ℝ) ^ (-3/2 : ℝ)) := by
      have h_eq : (fun m : ℕ => 4 * (m : ℝ) ^ (-3/2 : ℝ)) =
          (fun m : ℕ => (4 : ℝ) • (m : ℝ) ^ (-3/2 : ℝ)) := by funext m; simp [smul_eq_mul]
      rw [h_eq]
      obtain ⟨a, ha⟩ := h_rpow_sum
      exact ⟨4 * a, ha.const_smul (4 : ℝ)⟩
    refine Summable.of_nonneg_of_le ?_ ?_ h4_sum
    · intro m
      by_cases h01 : m = 0 ∨ m = 1
      · simp [h01]
      · simp [h01]; positivity
    · intro m
      by_cases h01 : m = 0 ∨ m = 1
      · simp [h01]; positivity
      · simp [h01]
  -- Nonnegativity of inner tsum
  have h_inner_nonneg : ∀ m, 0 ≤ ∑' j : ℕ, Hpp (m, j) := by
    intro m
    rw [h_inner_tsum]
    split_ifs with hp
    · have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hp.pos
      have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hp.one_lt
      have hm_sub1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      apply mul_nonneg
      · apply div_nonneg
        · exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ (m : ℝ))
        · positivity
      · apply div_nonneg (by positivity) (by linarith)
    · norm_num
  -- Final comparison
  exact Summable.of_nonneg_of_le h_inner_nonneg h_bound h_summable_bound

lemma Hpp_summable : Summable Hpp := by
  -- summable_prod_of_nonneg: Summable f ↔ (∀ x, Summable (fun y ↦ f(x,y))) ∧ Summable (fun x ↦ ∑' y, f(x,y))
  have h_nonneg : ∀ mj, 0 ≤ Hpp mj := Hpp_nonneg
  have h_inner : ∀ m, Summable (fun j => Hpp (m, j)) := Hpp_inner_summable
  have h_outer : Summable (fun m => ∑' j, Hpp (m, j)) := Hpp_outer_summable
  exact (summable_prod_of_nonneg h_nonneg).mpr ⟨h_inner, h_outer⟩

theorem primePower_contribution_bounded : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C := by
  -- All terms nonneg, so |sum| = sum
  have h_abs : ∀ (x : ℝ), 2 ≤ x →
      |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ)| =
      ∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) := by
    intro x hx
    rw [abs_of_nonneg]
    apply Finset.sum_nonneg
    intro n hn
    exact vm_nonneg n
  use ∑' mj : ℕ × ℕ, Hpp mj
  intro x hx
  rw [h_abs x hx]
  -- Step 1: filter Λ(n)/n is same as filter Λ(n)/n with IsPrimePow added
  -- (since Λ(n) = 0 for non-prime-power)
  let S := Finset.Icc 2 ⌊x⌋₊ |>.filter (fun n => ¬Nat.Prime n)
  let Spp := S.filter (fun n => IsPrimePow n)
  have h_sum_eq : ∑ n ∈ S, (vonMangoldt n : ℝ) / (n : ℝ) =
      ∑ n ∈ Spp, (vonMangoldt n : ℝ) / (n : ℝ) := by
    have h_sub : Spp ⊆ S := Finset.filter_subset _ _
    refine (Finset.sum_sdiff h_sub).symm.trans ?_
    have h_zero_sum : ∑ n ∈ S \ Spp, (vonMangoldt n : ℝ) / (n : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have ⟨hS, hNotSpp⟩ : n ∈ S ∧ n ∉ Spp := Finset.mem_sdiff.mp hn
      have : ¬IsPrimePow n := by
        intro hpp
        exact hNotSpp (Finset.mem_filter.mpr ⟨hS, hpp⟩)
      have : vonMangoldt n = 0 := by rw [vonMangoldt_eq_zero_iff]; exact this
      simp [this]
    rw [h_zero_sum, zero_add]
  rw [h_sum_eq]
  -- Step 2: Each n in S with IsPrimePow is p^k with k≥2 (not prime)
  -- Map n → (n.minFac, n.factorization n.minFac - 2) injectively
  -- Λ(n)/n = (log p)/p^k = Hpp(p, k-2)
  -- Bound: ∑_{n} Λ(n)/n ≤ ∑'_{mj} Hpp(mj)
  -- Use: finite sum ≤ tsum for nonneg summable function
  have h_finite_le_tsum :
      ∑ n ∈ Spp, (vonMangoldt n : ℝ) / (n : ℝ)
      ≤ ∑' mj : ℕ × ℕ, Hpp mj := by
    -- Define the injection image as a finset in ℕ × ℕ
    let img := Spp.image
      (fun n => (n.minFac, n.factorization n.minFac - 2))
    -- Show pointwise: Λ(n)/n ≤ Hpp(n.minFac, n.factorization n.minFac - 2)
    have h_pointwise : ∑ n ∈ Spp, (vonMangoldt n : ℝ) / (n : ℝ)
        ≤ ∑' mj : ℕ × ℕ, Hpp mj := by
      let f : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac - 2)
      -- Show f is injective on Spp (as InjOn)
      have hf_inj_on : Set.InjOn f (Spp : Set ℕ) := by
        intro n₁ hn₁ n₂ hn₂ heq
        have hpp₁ : IsPrimePow n₁ := (Finset.mem_filter.mp hn₁).2
        have hpp₂ : IsPrimePow n₂ := (Finset.mem_filter.mp hn₂).2
        have n₁_ge_2 : 2 ≤ n₁ := by
          have : n₁ ∈ Finset.Icc 2 ⌊x⌋₊ := by
            have := (Finset.mem_filter.mp ((Finset.mem_filter.mp hn₁).1 : n₁ ∈ S)).1
            simpa [S] using this
          exact Finset.mem_Icc.mp this |>.1
        have n₂_ge_2 : 2 ≤ n₂ := by
          have : n₂ ∈ Finset.Icc 2 ⌊x⌋₊ := by
            have := (Finset.mem_filter.mp ((Finset.mem_filter.mp hn₂).1 : n₂ ∈ S)).1
            simpa [S] using this
          exact Finset.mem_Icc.mp this |>.1
        have h_mf : n₁.minFac = n₂.minFac := (Prod.mk.inj heq).1
        have h_fac : n₁.factorization n₁.minFac - 2 = n₂.factorization n₂.minFac - 2 :=
          by simpa [h_mf] using (Prod.mk.inj heq).2
        -- factorization values are positive
        have hp₁ : 0 < n₁.factorization n₁.minFac := by
          by_contra hk
          have h0 : n₁.factorization n₁.minFac = 0 := by omega
          have hn_val : n₁ = n₁.minFac ^ 0 :=
            congrArg (fun k => n₁.minFac ^ k) h0 ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp₁).symm
          have : n₁ = 1 := by rwa [pow_zero] at hn_val
          omega
        have hp₂ : 0 < n₂.factorization n₂.minFac := by
          by_contra hk
          have h0 : n₂.factorization n₂.minFac = 0 := by omega
          have hn_val : n₂ = n₂.minFac ^ 0 :=
            congrArg (fun k => n₂.minFac ^ k) h0 ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp₂).symm
          have : n₂ = 1 := by rwa [pow_zero] at hn_val
          omega
        -- k ≥ 2 for non-prime IsPrimePow
        have k₁_ge_2 : 2 ≤ n₁.factorization n₁.minFac := by
          have hNotP₁ : ¬Nat.Prime n₁ := by
            simpa [S] using (Finset.mem_filter.mp ((Finset.mem_filter.mp hn₁).1 : n₁ ∈ S)).2
          by_contra! hk
          have : n₁.factorization n₁.minFac ≤ 1 := by omega
          have hk1 : n₁.factorization n₁.minFac = 1 := by omega
          have hn_val : n₁ = n₁.minFac ^ 1 :=
            congrArg (fun k => n₁.minFac ^ k) hk1 ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp₁).symm
          -- n₁.minFac is prime (since n₁ ≠ 1)
          have hp₁ : Nat.Prime n₁.minFac := Nat.minFac_prime (by omega : n₁ ≠ 1)
          -- n₁ = n₁.minFac ^ 1 = n₁.minFac, so Nat.Prime n₁ follows
          have : n₁.minFac = n₁ := by rw [← pow_one n₁.minFac, ← hn_val]
          have : Nat.Prime n₁ := this ▸ hp₁
          exact hNotP₁ this
        have k₂_ge_2 : 2 ≤ n₂.factorization n₂.minFac := by
          have hNotP₂ : ¬Nat.Prime n₂ := by
            simpa [S] using (Finset.mem_filter.mp ((Finset.mem_filter.mp hn₂).1 : n₂ ∈ S)).2
          by_contra! hk
          have : n₂.factorization n₂.minFac ≤ 1 := by omega
          have hk1 : n₂.factorization n₂.minFac = 1 := by omega
          have hn_val : n₂ = n₂.minFac ^ 1 :=
            congrArg (fun k => n₂.minFac ^ k) hk1 ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp₂).symm
          have hp₂ : Nat.Prime n₂.minFac := Nat.minFac_prime (by omega : n₂ ≠ 1)
          have : n₂.minFac = n₂ := by rw [← pow_one n₂.minFac, ← hn_val]
          have : Nat.Prime n₂ := this ▸ hp₂
          exact hNotP₂ this
        have h_fac_eq : n₁.factorization n₁.minFac = n₂.factorization n₂.minFac := by omega
        -- n₁ = p^k = n₂
        calc n₁ = n₁.minFac ^ n₁.factorization n₁.minFac :=
            (IsPrimePow.minFac_pow_factorization_eq hpp₁).symm
          _ = n₂ := by
            have h1 : n₁.minFac ^ n₁.factorization n₁.minFac =
                n₂.minFac ^ n₁.factorization n₁.minFac := by nth_rw 1 [h_mf]
            have h2 : n₂.minFac ^ n₁.factorization n₁.minFac =
                n₂.minFac ^ n₂.factorization n₂.minFac := by rw [h_fac_eq]
            have : n₁.minFac ^ n₁.factorization n₁.minFac =
                n₂.minFac ^ n₂.factorization n₂.minFac := h1.trans h2
            rwa [IsPrimePow.minFac_pow_factorization_eq hpp₂] at this
      have h_pointwise_eq : ∑ n ∈ Spp, (vonMangoldt n : ℝ) / (n : ℝ) =
          ∑ n ∈ Spp, Hpp (f n) := by
        apply Finset.sum_congr rfl
        intro n hn
        -- (vonMangoldt n)/n = Hpp(f(n)) for n ∈ Spp
        have hpp : IsPrimePow n := (Finset.mem_filter.mp hn).2
        have hS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hNotPrime : ¬Nat.Prime n := by
          simpa [S] using (Finset.mem_filter.mp hS).2
        have n_ge_2 : 2 ≤ n := by
          have : n ∈ Finset.Icc 2 ⌊x⌋₊ := by
            have := (Finset.mem_filter.mp hS).1
            simpa [S] using this
          exact Finset.mem_Icc.mp this |>.1
        have n_ne_1 : n ≠ 1 := by omega
        have p_prime : Nat.Prime n.minFac := Nat.minFac_prime n_ne_1
        have k_ge_2 : 2 ≤ n.factorization n.minFac := by
          by_contra! hk
          have hk_le : n.factorization n.minFac ≤ 1 := by omega
          have hk_pos : 0 < n.factorization n.minFac := by
            by_contra h
            have : n.factorization n.minFac = 0 := by omega
            have : n = n.minFac ^ 0 := congrArg (fun k => n.minFac ^ k) this ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp).symm
            have : n = 1 := by simpa using this
            omega
          have hk1 : n.factorization n.minFac = 1 := by omega
          have hn_val : n = n.minFac ^ 1 :=
            congrArg (fun k => n.minFac ^ k) hk1 ▸
              (IsPrimePow.minFac_pow_factorization_eq hpp).symm
          have hp : Nat.Prime n.minFac := Nat.minFac_prime n_ne_1
          have : n.minFac = n := by rw [← pow_one n.minFac, ← hn_val]
          have : Nat.Prime n := this ▸ hp
          exact hNotPrime this
        have hk_ne : n.factorization n.minFac ≠ 0 := by omega
        -- vonMangoldt n = log (n.minFac)
        have h_vm : (vonMangoldt n : ℝ) = Real.log (n.minFac : ℝ) := by
          show (vonMangoldt n : ℝ) = Real.log (n.minFac : ℝ)
          have hn_val : n = n.minFac ^ n.factorization n.minFac :=
            (IsPrimePow.minFac_pow_factorization_eq hpp).symm
          rw [show vonMangoldt n = vonMangoldt (n.minFac ^ n.factorization n.minFac)
              from congrArg vonMangoldt hn_val]
          rw [vonMangoldt_apply_pow hk_ne]
          rw [vonMangoldt_apply_prime p_prime]
        -- n = minFac^k as reals
        have h_n_rpow : (n : ℝ) = (n.minFac : ℝ) ^ (n.factorization n.minFac) := by
          norm_cast
          exact (IsPrimePow.minFac_pow_factorization_eq hpp).symm
        -- Hpp(f(n)) computation
        have h_hpp : Hpp (f n) =
            Real.log (n.minFac : ℝ) / (n.minFac : ℝ) ^ (n.factorization n.minFac) := by
          simp only [f, Hpp_apply]
          rw [if_pos p_prime]
          have hk : n.factorization n.minFac - 2 + 2 = n.factorization n.minFac :=
            Nat.sub_add_cancel k_ge_2
          rw [congr_arg (fun k : ℕ => Real.log (n.minFac : ℝ) / (n.minFac : ℝ) ^ k) hk]
        rw [h_vm, h_n_rpow, h_hpp]
      rw [h_pointwise_eq]
      -- ∑ n ∈ Spp, Hpp (f n) = ∑ mj ∈ img, Hpp mj (by sum_bij + injectivity)
      have h_img_eq : ∑ n ∈ Spp, Hpp (f n) = ∑ mj ∈ img, Hpp mj := by
        apply Finset.sum_bij (fun n _ => f n)
        · intro n hn; simp [img]; exact ⟨n, hn, rfl⟩
        · intro n₁ hn₁ n₂ hn₂ heq; exact hf_inj_on hn₁ hn₂ heq
        · intro mj hmj; simp [img] at hmj; rcases hmj with ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
        · intro n hn; rfl
      -- ∑ mj ∈ img, Hpp mj ≤ ∑' mj, Hpp mj (finite sum ≤ tsum for nonneg summable)
      have h_img_le : ∑ mj ∈ img, Hpp mj ≤ ∑' mj : ℕ × ℕ, Hpp mj :=
        Hpp_summable.sum_le_tsum img (fun mj _ => Hpp_nonneg mj)
      -- Chain: = ∑ mj ∈ img ≤ ∑'
      calc ∑ n ∈ Spp, Hpp (f n) = ∑ mj ∈ img, Hpp mj := h_img_eq
        _ ≤ ∑' mj : ℕ × ℕ, Hpp mj := h_img_le
    exact h_pointwise
  exact h_finite_le_tsum

end

/-! === 第七部分: Mertens 定理 (3定理) === -/

theorem mertens_abel_identity (x : ℝ) (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) =
    ψ x / x + ∫ t in Set.Ioc 2 x, ψ t / (t * t) := by
  -- Step 1: Apply Abel summation with c = Λ, f(t) = t⁻¹
  have h_abel := sum_mul_eq_sub_integral_mul₁
    (c := fun n => (vonMangoldt n : ℝ))
    (f := fun t : ℝ => t⁻¹)
    (hc := vonMangoldt_zero)
    (hc1 := vonMangoldt_one)
    (b := x)
    (hf_diff := by
      intro z hz
      have : z ≥ 2 := hz.1
      have : z ≠ 0 := by linarith
      fun_prop)
    (hf_int := by
      have h_deriv_eq : deriv (fun t : ℝ => t⁻¹) = fun t : ℝ => -(t^2)⁻¹ := deriv_inv'
      rw [h_deriv_eq]
      have h_eq : (fun t : ℝ => -(t^2)⁻¹) = (fun t : ℝ => (-1 : ℝ) / (t^2)) := by
        funext t; simp [div_eq_mul_inv]
      rw [h_eq]
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le hx).symm.mpr ?_
      refine ContinuousOn.intervalIntegrable_of_Icc hx ?_
      refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
      intro z hz; have : z ≥ 2 := hz.1; have : z ≠ 0 := by linarith
      simpa [pow_eq_zero_iff] using this)
  -- Step 2: Convert to interval integral notation
  rw [← intervalIntegral.integral_of_le hx] at h_abel
  -- Step 3: Rewrite deriv (·⁻¹) = -(·²)⁻¹ and ∑Λ = ψ inside the integral
  have int_deriv : ∫ u in (2 : ℝ)..x, deriv (fun t : ℝ => t⁻¹) u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, (vonMangoldt k : ℝ) =
      ∫ u in (2 : ℝ)..x, -(u ^ 2)⁻¹ * ψ u := by
    apply intervalIntegral.integral_congr
    intro u _
    dsimp
    rw [deriv_inv, (Chebyshev.psi_eq_sum_Icc u).symm]
  rw [int_deriv] at h_abel
  -- Step 4: ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, Λ k = ψ x
  rw [(Chebyshev.psi_eq_sum_Icc x).symm] at h_abel
  -- Step 5: LHS: ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, k⁻¹ * Λ k = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, Λ(n)/n
  have h_lhs : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * (vonMangoldt k : ℝ) =
      ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) := by
    have h_sub : Finset.Icc 0 ⌊x⌋₊ = {0, 1} ∪ Finset.Icc 2 ⌊x⌋₊ := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      have hx_pos : (0 : ℝ) ≤ x := by linarith
      have hk_floor : k ≤ ⌊x⌋₊ ↔ (k : ℝ) ≤ x := Nat.le_floor_iff hx_pos
      have h_forward : 0 ≤ k ∧ k ≤ ⌊x⌋₊ → (k = 0 ∨ k = 1) ∨ 2 ≤ k ∧ k ≤ ⌊x⌋₊ := by
        intro h; have hk0 := h.1; have hkx := h.2
        by_cases hkl : k < 2
        · have : k = 0 ∨ k = 1 := by omega
          exact Or.inl this
        · have : 2 ≤ k := by omega
          exact Or.inr (And.intro this hkx)
      have h_backward : ((k = 0 ∨ k = 1) ∨ 2 ≤ k ∧ k ≤ ⌊x⌋₊) → 0 ≤ k ∧ k ≤ ⌊x⌋₊ := by
        intro h
        rcases h with (hk01 | ⟨hk2, hkx⟩)
        · rcases hk01 with (rfl | rfl)
          · exact And.intro (Nat.zero_le 0) (Nat.zero_le ⌊x⌋₊)
          · exact And.intro (Nat.zero_le 1) (hk_floor.mpr (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x)))
        · exact And.intro (by omega : 0 ≤ k) hkx
      constructor <;> intro h
      · exact h_forward h
      · exact h_backward h
    rw [h_sub]
    have h_disj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 ⌊x⌋₊) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      simp at hk1
      have hk_ge : 2 ≤ k := (Finset.mem_Icc.mp hk2).1
      cases hk1 with
      | inl h => linarith [hk_ge, h]
      | inr h => linarith [hk_ge, h]
    rw [Finset.sum_union h_disj]
    have h01 : ∑ k ∈ ({0, 1} : Finset ℕ), (k : ℝ)⁻¹ * (vonMangoldt k : ℝ) = 0 := by
      simp [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    rw [h01, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : k ≥ 2 := (Finset.mem_Icc.mp hk).1
    have hk_ne : (k : ℝ) ≠ 0 := by
      have : (k : ℝ) ≥ 2 := by exact_mod_cast hk2
      linarith
    field_simp [hk_ne]
  rw [h_lhs] at h_abel
  -- Step 6: Algebraic simplification
  have hx_ne : x ≠ 0 := by linarith
  have h_fx : x⁻¹ * ψ x = ψ x / x := by field_simp [hx_ne]
  rw [h_fx] at h_abel
  -- Convert back to Set.Ioc
  rw [intervalIntegral.integral_of_le hx] at h_abel
  -- Handle the negated integral
  have h_neg_int : -∫ t in Set.Ioc 2 x, -(t ^ 2)⁻¹ * ψ t =
      ∫ t in Set.Ioc 2 x, ψ t / (t * t) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht_pos : t > 0 := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    field_simp [ht_ne, pow_two]
  -- Final step: rewrite goal using h_neg_int and h_abel
  have h_final : ψ x / x - ∫ t in Set.Ioc 2 x, -(t ^ 2)⁻¹ * ψ t =
      ψ x / x + ∫ t in Set.Ioc 2 x, ψ t / (t * t) := by
    rw [← h_neg_int]
    ring
  rw [← h_final]
  convert h_abel

/-! ### 辅助引理: 对数求和 -/

lemma log_sum_bound (N : ℕ) (hN : 2 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1)| ≤ Real.log (N : ℝ) := by
  have h1N : (1 : ℕ) ≤ N := by omega
  have h_log_mono : MonotoneOn Real.log (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    refine Real.log_le_log (by nlinarith [hx.1]) hxy
  have h_int_eq : ∫ x in (1 : ℝ)..(N : ℝ), Real.log x = (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
    rw [integral_log]
    simp
  -- Icc 1 N = Ico 1 N ∪ {N}
  have h_Icc_split : (Finset.Icc (1 : ℕ) N : Finset ℕ) = Finset.Ico (1 : ℕ) N ∪ {(N : ℕ)} := by
    ext n; simp; omega
  have h_disj : Disjoint (Finset.Ico (1 : ℕ) N) ({(N : ℕ)} : Finset ℕ) := by
    simp [Finset.disjoint_left]; omega
  have h_Icc_sum_eq : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      (∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ)) + Real.log (N : ℝ) := by
    calc
      ∑ n ∈ Finset.Icc (1 : ℕ) N, Real.log (n : ℝ) =
          ∑ n ∈ (Finset.Ico (1 : ℕ) N ∪ {(N : ℕ)}), Real.log (n : ℝ) := by rw [h_Icc_split]
      _ = (∑ n ∈ Finset.Ico (1 : ℕ) N, Real.log (n : ℝ)) + (∑ n ∈ ({(N : ℕ)} : Finset ℕ), Real.log (n : ℝ)) :=
        Finset.sum_union h_disj
      _ = (∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ)) + Real.log (N : ℝ) := by simp
  have h_image : (Finset.Ico (1 : ℕ) N).image (fun i : ℕ => i + 1) = Finset.Icc (2 : ℕ) N := by
    ext j; simp [Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc]
  -- Lower bound using integral
  have h_lower : ∫ x in (1 : ℝ)..(N : ℝ), Real.log x ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
    have h_temp := MonotoneOn.integral_le_sum_Ico (f := Real.log) h1N (by
      simpa using h_log_mono)
    have h_sum_shift : ∑ i ∈ Finset.Ico (1 : ℕ) N, Real.log (((i + 1 : ℕ) : ℝ)) = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
      calc
        ∑ i ∈ Finset.Ico (1 : ℕ) N, Real.log (((i + 1 : ℕ) : ℝ)) =
            ∑ j ∈ (Finset.Ico (1 : ℕ) N).image (fun i : ℕ => i + 1), Real.log (j : ℝ) := by
          rw [Finset.sum_image (fun i hi j hj h => by omega)]
        _ = ∑ j ∈ Finset.Icc (2 : ℕ) N, Real.log (j : ℝ) := by rw [h_image]
        _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
          refine Finset.sum_subset (fun x hx => ?_) (by
            intro x hx hx'
            rcases Finset.mem_Icc.mp hx with ⟨hx_low, hx_up⟩
            have hx_lt_2 : x < 2 := by
              by_contra! h
              exact hx' (Finset.mem_Icc.mpr ⟨h, hx_up⟩)
            have hx_eq_1 : x = 1 := by omega
            subst hx_eq_1; simp
          )
          rcases Finset.mem_Icc.mp hx with ⟨hx_low, hx_up⟩
          exact Finset.mem_Icc.mpr ⟨by omega, hx_up⟩
    calc
      ∫ x in (1 : ℝ)..(N : ℝ), Real.log x ≤ ∑ i ∈ Finset.Ico (1 : ℕ) N, Real.log (((i + 1 : ℕ) : ℝ)) := by
        simpa using h_temp
      _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := h_sum_shift
  -- Upper bound using integral
  have h_upper : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ (∫ x in (1 : ℝ)..(N : ℝ), Real.log x) + Real.log (N : ℝ) := by
    rw [h_Icc_sum_eq]
    have h_temp2 : ∑ i ∈ Finset.Ico (1 : ℕ) N, Real.log (i : ℝ) ≤ ∫ x in (1 : ℝ)..(N : ℝ), Real.log x := by
      have h := MonotoneOn.sum_le_integral_Ico (f := Real.log) h1N (by simpa using h_log_mono)
      have h_eq : ∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), Real.log x = ∫ x in (1 : ℝ)..(N : ℝ), Real.log x := by
        simp
      exact h.trans h_eq.le
    gcongr
  have h_log_N_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hN_ge_1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1N
    exact Real.log_nonneg hN_ge_1
  rw [abs_le]
  constructor
  · -- -(log N) ≤ ∑ log n - (N*log N - N + 1)
    have : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
      linarith
    linarith
  · -- ∑ log n - (N*log N - N + 1) ≤ log N
    calc
      ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) ≤
          ((∫ x in (1 : ℝ)..(N : ℝ), Real.log x) + Real.log (N : ℝ)) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) :=
        sub_le_sub_right h_upper _
      _ = (((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) + Real.log (N : ℝ)) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1) := by rw [h_int_eq]
      _ = Real.log (N : ℝ) := by ring_nf

/-! ### 辅助引理: Mertens 第一定理 -/

-- 卷积恒等式: ∑_{n=1}^N Λ(n)*⌊N/n⌋ = ∑_{n=1}^N log n
lemma conv_identity (N : ℕ) : ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) =
    ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by
  calc
    ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) =
        ∑ n ∈ Finset.Ioc 0 N, ((vonMangoldt * ArithmeticFunction.zeta) n : ℝ) := by
      rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum vonMangoldt N]
    _ = ∑ n ∈ Finset.Ioc 0 N, (Real.log (n : ℝ)) := by
      simp [ArithmeticFunction.vonMangoldt_mul_zeta]

lemma decomp_sum (N : ℕ) : (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) =
    ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) +
    ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by
  calc
    (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) =
        ∑ n ∈ Finset.Ioc 0 N, (N : ℝ) * ((vonMangoldt n : ℝ) / (n : ℝ)) := by rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ)) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn_pos : (n : ℝ) ≠ 0 := by
        have hm := Finset.mem_Ioc.mp hn
        exact mod_cast hm.1.ne'
      field_simp [hn_pos, mul_comm]
    _ = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * (((N / n : ℕ) : ℝ) + ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      ring
    _ = ∑ n ∈ Finset.Ioc 0 N, ((vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) + (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      ring
    _ = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) +
        ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib]

-- 误差项有界: |N/n - ⌊N/n⌋| < 1
lemma frac_bound (N n : ℕ) (hn : n ≠ 0) : |(N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)| < 1 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN_mod_eq : (N : ℝ) - ((N / n : ℕ) : ℝ) * (n : ℝ) = ((N % n : ℕ) : ℝ) := by
    have hN_eq : (N : ℝ) = ((N / n : ℕ) : ℝ) * (n : ℝ) + ((N % n : ℕ) : ℝ) := by
      calc
        (N : ℝ) = ((N : ℕ) : ℝ) := by norm_cast
        _ = ((N / n * n + N % n : ℕ) : ℝ) := by
          norm_cast
          exact (by simpa [mul_comm] using (Nat.div_add_mod N n).symm)
        _ = ((N / n : ℕ) : ℝ) * (n : ℝ) + ((N % n : ℕ) : ℝ) := by simp
    linarith
  have h_eq : (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) = ((N % n : ℕ) : ℝ) / (n : ℝ) := by
    field_simp [hpos.ne']
    nlinarith
  rw [h_eq]
  have h_mod_lt_n : (N % n : ℕ) < n := Nat.mod_lt N (Nat.pos_of_ne_zero hn)
  have h_ratio_nonneg : 0 ≤ ((N % n : ℕ) : ℝ) / (n : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (by positivity)
  have h_ratio_lt_one : ((N % n : ℕ) : ℝ) / (n : ℝ) < 1 := by
    refine (div_lt_one hpos).mpr ?_
    exact_mod_cast h_mod_lt_n
  rw [abs_of_nonneg h_ratio_nonneg]
  exact h_ratio_lt_one

-- ∑ Λ(n)*(N/n - ⌊N/n⌋) ≤ ψ(N)
lemma error_bound (N : ℕ) : |∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))| ≤ ψ (N : ℝ) := by
  have h_nonneg_vM : ∀ n, 0 ≤ (vonMangoldt n : ℝ) := by
    intro n; exact mod_cast (vonMangoldt_nonneg (n := n))
  have h_frac_nonneg (n : ℕ) : 0 ≤ (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) := by
    by_cases hn : n = 0
    · subst hn; simp
    · have h_eq : (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) = ((N % n : ℕ) : ℝ) / (n : ℝ) := by
        have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        field_simp [hpos.ne']
        have hN_eq : (N : ℝ) = ((N / n : ℕ) : ℝ) * (n : ℝ) + ((N % n : ℕ) : ℝ) := by
          calc
            (N : ℝ) = ((N : ℕ) : ℝ) := by norm_cast
            _ = ((N / n * n + N % n : ℕ) : ℝ) := by
              norm_cast
              simpa [mul_comm] using (Nat.div_add_mod N n).symm
            _ = ((N / n : ℕ) : ℝ) * (n : ℝ) + ((N % n : ℕ) : ℝ) := by simp
        nlinarith
      rw [h_eq]
      apply div_nonneg
      · exact mod_cast Nat.zero_le _
      · positivity
  have h_term_nonneg (n : ℕ) : 0 ≤ (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) :=
    mul_nonneg (h_nonneg_vM n) (h_frac_nonneg n)
  have h_sum_nonneg : 0 ≤ ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) :=
    Finset.sum_nonneg (fun n hn => h_term_nonneg n)
  rw [abs_of_nonneg h_sum_nonneg]
  calc
    ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))
        ≤ ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * 1 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn_ne_zero : n ≠ 0 := by
        intro hzero; have := Finset.mem_Ioc.mp hn; omega
      have h_frac_lt_one : (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) < 1 := by
        have h_bound := frac_bound N n hn_ne_zero
        rw [abs_of_nonneg (h_frac_nonneg n)] at h_bound
        exact h_bound
      refine mul_le_mul_of_nonneg_left (by linarith) (h_nonneg_vM n)
    _ = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) := by simp
    _ = ψ (N : ℝ) := by rw [psi_nat_eq_sum]

-- ∑ Λ(n)/n - log N 有界
lemma vm_div_sum_sub_log_bound (N : ℕ) (hN : 2 ≤ N) :
    |∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log (N : ℝ)| ≤ Real.log 4 + 7 := by
  have hN_pos : (N : ℝ) > 0 := by exact_mod_cast (show 0 < N from by omega)
  have h_psi_bound : ψ (N : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by
    have h_nonneg : 0 ≤ ψ (N : ℝ) := Chebyshev.psi_nonneg (N : ℝ)
    have h_bound := psi_bounded (N : ℝ) (by positivity : 0 ≤ (N : ℝ))
    rwa [abs_of_nonneg h_nonneg] at h_bound
  have h_conv_comb : |(N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ)| ≤ ψ (N : ℝ) := by
    have h_eq : (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) =
        ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by
      calc
        (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) =
            (∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N / n : ℕ) : ℝ) +
             ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))) -
            ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by rw [decomp_sum N]
        _ = (∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) +
             ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))) -
            ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by rw [conv_identity N]
        _ = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) * ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ)) := by ring
    rw [h_eq]
    exact error_bound N
  have h_Ioc_eq_Icc : Finset.Ioc (0 : ℕ) N = Finset.Icc (1 : ℕ) N := by
    ext n; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have h_log_sum : |∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1)| ≤ Real.log (N : ℝ) := by
    rw [h_Ioc_eq_Icc]
    exact log_sum_bound N hN
  -- Main computation: bound |S - log N|
  -- |S - log N| ≤ |S - T/N| + |T/N - log N|
  let S := ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ)
  let T := ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ)
  have hS_div : |(N : ℝ) * S - T| ≤ ψ (N : ℝ) := h_conv_comb
  have hS_sub_T_div_N : |S - T / (N : ℝ)| ≤ (Real.log 4 + 4) := by
    have h_eq : S - T / (N : ℝ) = ((N : ℝ) * S - T) / (N : ℝ) := by
      field_simp [hN_pos.ne', mul_comm]
    rw [h_eq]
    rw [abs_div, abs_of_pos hN_pos]
    calc
      |(N : ℝ) * S - T| / (N : ℝ) = |(N : ℝ) * S - T| * (1 / (N : ℝ)) := by ring
      _ ≤ ψ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right hS_div (by positivity)
      _ = ψ (N : ℝ) / (N : ℝ) := by ring
      _ = ψ (N : ℝ) * (1 / (N : ℝ)) := by ring
      _ ≤ ((Real.log 4 + 4) * (N : ℝ)) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right h_psi_bound (by positivity)
      _ = ((Real.log 4 + 4) * (N : ℝ)) / (N : ℝ) := by ring
      _ = Real.log 4 + 4 := by field_simp [hN_pos.ne']
  have h_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : -|a| ≤ a := neg_abs_le a
    have h3 : b ≤ |b| := le_abs_self b
    have h4 : -|b| ≤ b := neg_abs_le b
    have hab1 : a + b ≤ |a| + |b| := add_le_add h1 h3
    have hab2 : -(|a| + |b|) ≤ a + b := by linarith
    exact abs_le.mpr ⟨hab2, hab1⟩
  have h_T_div_N_sub_log : |T / (N : ℝ) - Real.log (N : ℝ)| ≤ 3 := by
    let A := (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1
    have h_log_bound : |T - A| ≤ Real.log (N : ℝ) := h_log_sum
    have h_log_N_div_N_le_one : Real.log (N : ℝ) / (N : ℝ) ≤ 1 := by
      calc
        Real.log (N : ℝ) / (N : ℝ) = Real.log (N : ℝ) * (1 / (N : ℝ)) := by ring
        _ ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right (Real.log_le_self (by positivity : 0 ≤ (N : ℝ))) (by positivity)
        _ = 1 := by field_simp [hN_pos.ne']
    have h_one_div_N_le_half : 1 / (N : ℝ) ≤ 1/2 := by
      have hN_large : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact (one_div_le_one_div (by positivity : 0 < (N : ℝ)) (by norm_num : 0 < (2 : ℝ))).mpr hN_large
    have h_one_div_N_nonneg : 0 ≤ 1 / (N : ℝ) := div_nonneg (by norm_num) (by positivity)
    calc
      |T / (N : ℝ) - Real.log (N : ℝ)| = |(T - A) / (N : ℝ) - 1 + 1 / (N : ℝ)| := by
        have h_inner_eq : T / (N : ℝ) - Real.log (N : ℝ) = (T - A) / (N : ℝ) - 1 + 1 / (N : ℝ) := by
          field_simp [hN_pos.ne', A]
          ring
        rw [h_inner_eq]
      _ ≤ |(T - A) / (N : ℝ) - 1| + |1 / (N : ℝ)| := h_triangle _ _
      _ ≤ (|(T - A) / (N : ℝ)| + |(1 : ℝ)|) + |1 / (N : ℝ)| := by
        have h_temp : |(T - A) / (N : ℝ) - 1| ≤ |(T - A) / (N : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h_temp (|1 / (N : ℝ)|)
      _ = |(T - A) / (N : ℝ)| + 1 + |1 / (N : ℝ)| := by simp
      _ = |T - A| / |(N : ℝ)| + 1 + |1 / (N : ℝ)| := by rw [abs_div]
      _ = |T - A| / (N : ℝ) + 1 + |1 / (N : ℝ)| := by rw [abs_of_pos hN_pos]
      _ = |T - A| / (N : ℝ) + 1 + (1 / (N : ℝ)) := by rw [abs_of_nonneg h_one_div_N_nonneg]
      _ ≤ Real.log (N : ℝ) / (N : ℝ) + 1 + (1 / (N : ℝ)) := by
        have h_mid : |T - A| / (N : ℝ) ≤ Real.log (N : ℝ) / (N : ℝ) := by
          calc
            |T - A| / (N : ℝ) = |T - A| * (1 / (N : ℝ)) := by ring
            _ ≤ Real.log (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right h_log_bound (by positivity)
            _ = Real.log (N : ℝ) / (N : ℝ) := by ring
        linarith
      _ ≤ 1 + 1 + (1 / (N : ℝ)) := by linarith
      _ ≤ 1 + 1 + (1/2 : ℝ) := by linarith
      _ = (2.5 : ℝ) := by norm_num
      _ ≤ 3 := by norm_num
  calc
    |S - Real.log (N : ℝ)| = |(S - T / (N : ℝ)) + (T / (N : ℝ) - Real.log (N : ℝ))| := by ring
    _ ≤ |S - T / (N : ℝ)| + |T / (N : ℝ) - Real.log (N : ℝ)| := by
      apply h_triangle
    _ ≤ (Real.log 4 + 4) + 3 := by gcongr
    _ = Real.log 4 + 7 := by ring

/-! ### Mertens 第一定理 (主定理) -/

theorem mertens_first_theorem_bounded : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ (Finset.Ioc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log x| ≤ C := by
  rcases primePower_contribution_bounded with ⟨C₁, hC₁⟩
  let C := Real.log 4 + 7 + C₁ + Real.log 2
  refine ⟨C, ?_⟩
  intro x hx
  set N := ⌊x⌋₊ with hN_def
  have hN_ge_2 : 2 ≤ N := by
    by_contra! h
    have hN_le_1 : N ≤ 1 := by omega
    have hx_lt_2 : x < 2 := by
      calc
        x < (N : ℝ) + 1 := by exact mod_cast Nat.lt_floor_add_one x
        _ ≤ (1 : ℝ) + 1 := by
          have hN_cast : (N : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hN_le_1
          nlinarith
        _ = 2 := by norm_num
    linarith
  have hN_pos : (0 : ℕ) < N := by omega
  have hN_ne_zero : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hx_pos : x > 0 := by linarith
  have hx_ne_zero : x ≠ 0 := by linarith
  have h_int_bound : |∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log (N : ℝ)| ≤ Real.log 4 + 7 :=
    vm_div_sum_sub_log_bound N hN_ge_2
  have h_nonprime_bound : |∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C₁ := by
    have h_eq_sum : ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ) =
        ∑ n ∈ (Finset.Icc 2 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ) := by
      apply (Finset.sum_subset ?_ ?_).symm
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hn_mem, hn_notprime⟩
        rcases Finset.mem_Icc.mp hn_mem with ⟨hn_ge_2, hn_le_N⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hn_le_N⟩, hn_notprime⟩
      · intro n hn hn'
        rcases Finset.mem_filter.mp hn with ⟨hn_mem, hn_notprime⟩
        rcases Finset.mem_Ioc.mp hn_mem with ⟨hn_gt_0, hn_le_N⟩
        have hn_lt_2 : n < 2 := by
          by_contra! h
          have hn_ge_2' : 2 ≤ n := h
          have hmem : n ∈ (Finset.Icc 2 N).filter (fun n => ¬Nat.Prime n) :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn_ge_2', hn_le_N⟩, hn_notprime⟩
          exact hn' hmem
        have hn1 : n = 1 := by omega
        subst hn1; simp
    rw [h_eq_sum]
    have hxC₁ : 2 ≤ (N : ℝ) := by exact_mod_cast hN_ge_2
    have hC₁_N := hC₁ (N : ℝ) hxC₁
    simpa [Nat.floor_natCast] using hC₁_N
  have h_sdiff : (Finset.Ioc 0 N) \ (Finset.Ioc 0 N).filter Nat.Prime =
      (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n) := by
    ext n; simp [Finset.mem_sdiff, Finset.mem_filter]; tauto
  have h_sum_split : ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) =
      (∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ)) +
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) := by
    have h_sub : (Finset.Ioc 0 N).filter Nat.Prime ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
    have h_vm_to_log : (∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, (vonMangoldt n : ℝ) / (n : ℝ)) =
        (∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      rw [vonMangoldt_apply_prime hprime]
    calc
      ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) =
          (∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, (vonMangoldt n : ℝ) / (n : ℝ)) +
          ∑ n ∈ (Finset.Ioc 0 N) \ (Finset.Ioc 0 N).filter Nat.Prime, (vonMangoldt n : ℝ) / (n : ℝ) := by
        simpa using Finset.sum_sdiff (f := fun (n : ℕ) => (vonMangoldt n : ℝ) / (n : ℝ)) h_sub
      _ = (∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, (vonMangoldt n : ℝ) / (n : ℝ)) +
          (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) := by rw [h_sdiff]
      _ = (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) +
          (∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime, (vonMangoldt n : ℝ) / (n : ℝ)) := by ring
      _ = (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) +
          (∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ)) := by rw [h_vm_to_log]
      _ = (∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ)) +
          (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) := by ring
  have h_prime_int_bound : |∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log (N : ℝ)| ≤ Real.log 4 + 7 + C₁ := by
    have h_sum_eq : (∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ)) - Real.log (N : ℝ) =
        ((∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log (N : ℝ)) -
        (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)) := by
      rw [h_sum_split]
      ring
    rw [h_sum_eq]
    calc
      |(∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log (N : ℝ)) -
        (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ))| ≤
        |∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log (N : ℝ)| +
        |∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬Nat.Prime n), (vonMangoldt n : ℝ) / (n : ℝ)| := abs_sub _ _
      _ ≤ (Real.log 4 + 7) + C₁ := by gcongr
  have h_log_diff : |Real.log (N : ℝ) - Real.log x| ≤ Real.log 2 := by
    have hNx : (N : ℝ) ≤ x := by
      have hx_nonneg : 0 ≤ x := by linarith
      have h_floor_le := Nat.floor_le hx_nonneg
      -- h_floor_le: (⌊x⌋₊ : ℝ) ≤ x
      rw [hN_def]
      exact h_floor_le
    have hxN : x < (N : ℝ) + 1 := by exact mod_cast Nat.lt_floor_add_one x
    have h_diff_nonpos : Real.log (N : ℝ) - Real.log x ≤ 0 := by
      rw [sub_nonpos]
      exact Real.log_le_log (by positivity) hNx
    rw [abs_of_nonpos h_diff_nonpos, neg_sub]
    have hx_div_N_lt_two : x / (N : ℝ) < 2 := by
      have hN_pos' : (0 : ℝ) < (N : ℝ) := by positivity
      calc
        x / (N : ℝ) < ((N : ℝ) + 1) / (N : ℝ) := by
          gcongr
        _ = 1 + 1 / (N : ℝ) := by
          field_simp [hN_pos'.ne']
        _ ≤ 1 + 1 / (2 : ℝ) := by
          have hN_ge_2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_2
          have h_div : 1 / (N : ℝ) ≤ 1 / (2 : ℝ) :=
            (one_div_le_one_div (by positivity : 0 < (N : ℝ)) (by norm_num : 0 < (2 : ℝ))).mpr hN_ge_2'
          nlinarith
        _ = 3/2 := by norm_num
        _ < 2 := by norm_num
    calc
      Real.log x - Real.log (N : ℝ) = Real.log (x / (N : ℝ)) := by
        rw [Real.log_div hx_ne_zero hN_ne_zero]
      _ ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)
  have h_final : |∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log x| ≤
      Real.log 4 + 7 + C₁ + Real.log 2 := by
    calc
      |∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log x| =
          |(∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log (N : ℝ)) +
            (Real.log (N : ℝ) - Real.log x)| := by ring
      _ ≤ |∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log (N : ℝ)| +
          |Real.log (N : ℝ) - Real.log x| := by
        have h_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
          have h1 : a ≤ |a| := le_abs_self a
          have h2 : -|a| ≤ a := neg_abs_le a
          have h3 : b ≤ |b| := le_abs_self b
          have h4 : -|b| ≤ b := neg_abs_le b
          have hab1 : a + b ≤ |a| + |b| := add_le_add h1 h3
          have hab2 : -(|a| + |b|) ≤ a + b := by linarith
          exact abs_le.mpr ⟨hab2, hab1⟩
        exact h_abs_add _ _
      _ ≤ (Real.log 4 + 7 + C₁) + Real.log 2 := by gcongr
      _ = Real.log 4 + 7 + C₁ + Real.log 2 := by ring
  have h_Ioc_fix : (Finset.Ioc 0 N).filter Nat.Prime = (Finset.Ioc 1 N).filter Nat.Prime := by
    ext p; constructor <;> intro hp
    · rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_prime⟩
      rcases Finset.mem_Ioc.mp hp_mem with ⟨hp_gt_0, hp_le_N⟩
      have hp_ge_1 : 1 < p := Nat.Prime.one_lt hp_prime
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioc.mpr ⟨by omega, hp_le_N⟩, hp_prime⟩
    · rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_prime⟩
      rcases Finset.mem_Ioc.mp hp_mem with ⟨hp_gt_1, hp_le_N⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioc.mpr ⟨by omega, hp_le_N⟩, hp_prime⟩
  rw [h_Ioc_fix] at h_final
  exact h_final

theorem mertens_first_theorem : (fun x : ℝ => ∑ p ∈ (Finset.Ioc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  rcases mertens_first_theorem_bounded with ⟨C, hC⟩
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx' : 2 ≤ x := hx
  calc
    |∑ p ∈ (Finset.Ioc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log p : ℝ) / (p : ℝ) - Real.log x| ≤ C := hC x hx'
    _ = C * ‖(1 : ℝ)‖ := by simp

/-! ### psi_integral_sub_log 的 O(1) 估计 -/

theorem psi_integral_sub_log_isBigO : (fun x : ℝ ↦ (∫ t in Set.Ioc 1 x, ψ t / (t * t)) - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  let C := (Real.log 4 + 7 + Real.log 2) + (Real.log 4 + 4)
  have hC_nonneg : 0 ≤ C := by
    have h_log4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have h_log2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx2 : 2 ≤ x := hx
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hN_ge_2 : 2 ≤ ⌊x⌋₊ := by
    by_contra! h
    have hN_le_1 : ⌊x⌋₊ ≤ 1 := by omega
    have hx_lt_2 : x < 2 := by
      calc
        x < (⌊x⌋₊ : ℝ) + 1 := by exact mod_cast Nat.lt_floor_add_one x
        _ ≤ (1 : ℝ) + 1 := by
          have h_cast : (⌊x⌋₊ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hN_le_1
          nlinarith
        _ = 2 := by norm_num
    linarith
  have hN_pos : (0 : ℕ) < ⌊x⌋₊ := by omega
  have hN_pos' : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hN_pos

  -- Integral over (1, 2] is zero because ψ t = 0 for t < 2 ({2} has measure zero)
  have h_int_12 : (∫ t in Set.Ioc (1 : ℝ) (2 : ℝ), ψ t / (t * t)) = 0 := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
    intro t ht
    have ht_lt_2 : t < 2 := Set.mem_Ioo.mp ht |>.2
    have hpsi : ψ t = 0 := psi_zero_of_lt_two' ht_lt_2
    simp [hpsi]

  -- Split the integral: (1, x] = (1, 2] ∪ (2, x]
  have h_disj_split : Disjoint (Set.Ioc (1 : ℝ) (2 : ℝ)) (Set.Ioc (2 : ℝ) x) := by
    apply Set.disjoint_left.mpr
    intro t ht1 ht2
    have h12 : t ≤ 2 := (Set.mem_Ioc.mp ht1).2
    have h22 : 2 < t := (Set.mem_Ioc.mp ht2).1
    linarith

  have h_int_split : (∫ t in Set.Ioc 1 x, ψ t / (t * t)) = (∫ t in Set.Ioc 2 x, ψ t / (t * t)) := by
    have h_union : (Set.Ioc (1 : ℝ) (2 : ℝ) ∪ Set.Ioc (2 : ℝ) x) = Set.Ioc (1 : ℝ) x :=
      Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (1 : ℝ) ≤ 2) hx2
    have h_meas_psi : Measurable ψ := Chebyshev.psi_mono.measurable
    have h_meas_denom : Measurable (fun t : ℝ => t * t) := (continuous_id.mul continuous_id).measurable
    have h_meas_f : Measurable (fun t : ℝ => ψ t / (t * t)) := h_meas_psi.div h_meas_denom
    have h_finite12 : MeasureTheory.volume (Set.Ioc (1 : ℝ) (2 : ℝ)) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have h_finite2x : MeasureTheory.volume (Set.Ioc (2 : ℝ) x) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have h_int12_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => ψ t / (t * t)) (Set.Ioc (1 : ℝ) (2 : ℝ)) := by
      refine MeasureTheory.volume.integrableOn_of_bounded (M := Real.log 4 + 4) h_finite12 h_meas_f.aestronglyMeasurable ?_
      refine Filter.mem_of_superset (MeasureTheory.self_mem_ae_restrict measurableSet_Ioc) ?_
      intro t ht
      rcases ht with ⟨ht1, ht2⟩
      have ht_ge1 : 1 ≤ t := by linarith
      have ht_nonneg : 0 ≤ t := by linarith
      have h_psi_abs : |ψ t| ≤ (Real.log 4 + 4) * t := psi_bounded t ht_nonneg
      have hpos : t * t > 0 := by nlinarith
      have h_div_bound : (Real.log 4 + 4) / t ≤ Real.log 4 + 4 := div_le_self (by positivity) ht_ge1
      calc
        ‖ψ t / (t * t)‖ = |ψ t / (t * t)| := by rw [Real.norm_eq_abs]
        _ = |ψ t| / |t * t| := by rw [abs_div]
        _ = |ψ t| / (t * t) := by rw [abs_of_pos hpos]
        _ ≤ ((Real.log 4 + 4) * t) / (t * t) := by gcongr
        _ = (Real.log 4 + 4) / t := by field_simp [show t ≠ 0 from by nlinarith]
        _ ≤ Real.log 4 + 4 := h_div_bound
    have h_int2x_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => ψ t / (t * t)) (Set.Ioc (2 : ℝ) x) := by
      refine MeasureTheory.volume.integrableOn_of_bounded (M := Real.log 4 + 4) h_finite2x h_meas_f.aestronglyMeasurable ?_
      refine Filter.mem_of_superset (MeasureTheory.self_mem_ae_restrict measurableSet_Ioc) ?_
      intro t ht
      rcases ht with ⟨ht2, htx⟩
      have ht_ge1 : 1 ≤ t := by linarith
      have ht_nonneg : 0 ≤ t := by linarith
      have h_psi_abs : |ψ t| ≤ (Real.log 4 + 4) * t := psi_bounded t ht_nonneg
      have hpos : t * t > 0 := by nlinarith
      have h_div_bound : (Real.log 4 + 4) / t ≤ Real.log 4 + 4 := div_le_self (by positivity) ht_ge1
      calc
        ‖ψ t / (t * t)‖ = |ψ t / (t * t)| := by rw [Real.norm_eq_abs]
        _ = |ψ t| / |t * t| := by rw [abs_div]
        _ = |ψ t| / (t * t) := by rw [abs_of_pos hpos]
        _ ≤ ((Real.log 4 + 4) * t) / (t * t) := by gcongr
        _ = (Real.log 4 + 4) / t := by field_simp [show t ≠ 0 from by linarith]
        _ ≤ Real.log 4 + 4 := h_div_bound
    calc
      (∫ t in Set.Ioc 1 x, ψ t / (t * t)) = (∫ t in (Set.Ioc (1 : ℝ) (2 : ℝ) ∪ Set.Ioc (2 : ℝ) x), ψ t / (t * t)) := by
        rw [h_union]
      _ = (∫ t in Set.Ioc (1 : ℝ) (2 : ℝ), ψ t / (t * t)) + (∫ t in Set.Ioc (2 : ℝ) x, ψ t / (t * t)) :=
        MeasureTheory.setIntegral_union h_disj_split measurableSet_Ioc h_int12_integrable h_int2x_integrable
      _ = (0 : ℝ) + (∫ t in Set.Ioc 2 x, ψ t / (t * t)) := by rw [h_int_12]
      _ = (∫ t in Set.Ioc 2 x, ψ t / (t * t)) := by simp

  -- Use Mertens-Abel identity to rewrite the (2, x] integral
  have h_int_2x : (∫ t in Set.Ioc 2 x, ψ t / (t * t)) =
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - ψ x / x := by
    linarith [mertens_abel_identity x hx2]

  -- Express the target quantity
  have h_expr : ((∫ t in Set.Ioc 1 x, ψ t / (t * t)) - Real.log x) =
      ((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x) - ψ x / x := by
    calc
      ((∫ t in Set.Ioc 1 x, ψ t / (t * t)) - Real.log x) = ((∫ t in Set.Ioc 2 x, ψ t / (t * t)) - Real.log x) := by rw [h_int_split]
      _ = (((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - ψ x / x) - Real.log x) := by rw [h_int_2x]
      _ = ((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x) - ψ x / x := by ring_nf

  rw [h_expr]

  -- Bound |∑ Λ/n - log x|
  have h_sum_log_bound : |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x| ≤ Real.log 4 + 7 + Real.log 2 := by
    have h_vm_bound : |∑ n ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| ≤ Real.log 4 + 7 :=
      vm_div_sum_sub_log_bound ⌊x⌋₊ hN_ge_2

    have h_sum_eq : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) =
        (∑ n ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) := by
      refine Finset.sum_subset ?_ ?_
      · intro n hn
        rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
        have hn0 : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn2
        exact Finset.mem_Ioc.mpr ⟨hn0, hnN⟩
      · intro n hn hn_not_mem
        rcases Finset.mem_Ioc.mp hn with ⟨hn0, hnN⟩
        have hn_lt_2 : n < 2 := by
          by_contra! h
          exact hn_not_mem (Finset.mem_Icc.mpr ⟨h, hnN⟩)
        have hn1 : n = 1 := by omega
        subst hn1; simp

    have h_log_diff : |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| ≤ Real.log 2 := by
      have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := by
        have hx_nonneg' : 0 ≤ x := hx_nonneg
        exact mod_cast Nat.floor_le hx_nonneg'
      have hxN : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by exact mod_cast Nat.lt_floor_add_one x
      have h_diff_nonpos : Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x ≤ 0 := by
        rw [sub_nonpos]
        exact Real.log_le_log (by positivity) hNx
      rw [abs_of_nonpos h_diff_nonpos, neg_sub]
      have hx_div_N_lt_two : x / ((⌊x⌋₊ : ℕ) : ℝ) < 2 := by
        calc
          x / ((⌊x⌋₊ : ℕ) : ℝ) < (((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ) := by
            gcongr
          _ = 1 + 1 / ((⌊x⌋₊ : ℕ) : ℝ) := by
            field_simp [hN_pos'.ne']
          _ ≤ 1 + 1 / (2 : ℝ) := by
            have hN_ge_2' : (2 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN_ge_2
            have h_div : 1 / ((⌊x⌋₊ : ℕ) : ℝ) ≤ 1 / (2 : ℝ) :=
              (one_div_le_one_div (by positivity : 0 < ((⌊x⌋₊ : ℕ) : ℝ)) (by norm_num : 0 < (2 : ℝ))).mpr hN_ge_2'
            nlinarith
          _ = 3/2 := by norm_num
          _ < 2 := by norm_num
      calc
        Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) = Real.log (x / ((⌊x⌋₊ : ℕ) : ℝ)) := by
          rw [← Real.log_div hx_pos.ne' hN_pos'.ne']
        _ ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)

    calc
      |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x|
          = |(∑ n ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x| := by rw [h_sum_eq]
      _ = |(∑ n ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)) +
            (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x)| := by ring_nf
      _ ≤ |∑ n ∈ Finset.Ioc (0 : ℕ) ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| +
            |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by
        have h_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
          have h1 : a ≤ |a| := le_abs_self a
          have h2 : -|a| ≤ a := neg_abs_le a
          have h3 : b ≤ |b| := le_abs_self b
          have h4 : -|b| ≤ b := neg_abs_le b
          have hab1 : a + b ≤ |a| + |b| := add_le_add h1 h3
          have hab2 : -(|a| + |b|) ≤ a + b := by linarith
          exact abs_le.mpr ⟨hab2, hab1⟩
        exact h_abs_add _ _
      _ ≤ (Real.log 4 + 7) + Real.log 2 := by gcongr
      _ = Real.log 4 + 7 + Real.log 2 := by ring

  -- Bound |ψ x / x|
  have h_psi_div_bound : |ψ x / x| ≤ Real.log 4 + 4 := by
    have h_psi_bound : |ψ x| ≤ (Real.log 4 + 4) * x := psi_bounded x hx_nonneg
    calc
      |ψ x / x| = |ψ x| / |x| := by rw [abs_div]
      _ = |ψ x| / x := by rw [abs_of_nonneg hx_nonneg]
      _ ≤ ((Real.log 4 + 4) * x) / x := by
        gcongr
      _ = Real.log 4 + 4 := by field_simp [hx_pos.ne']

  -- Triangle inequality
  have h_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : -|a| ≤ a := neg_abs_le a
    have h3 : b ≤ |b| := le_abs_self b
    have h4 : -|b| ≤ b := neg_abs_le b
    have hab1 : a + b ≤ |a| + |b| := add_le_add h1 h3
    have hab2 : -(|a| + |b|) ≤ a + b := by linarith
    exact abs_le.mpr ⟨hab2, hab1⟩

  calc
    |((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x) - ψ x / x|
        = |((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x) + (-(ψ x / x))| := by ring_nf
    _ ≤ |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x| + |-(ψ x / x)| := h_abs_add _ _
    _ = |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log x| + |ψ x / x| := by simp
    _ ≤ (Real.log 4 + 7 + Real.log 2) + (Real.log 4 + 4) := by gcongr
    _ = C := rfl
    _ = C * ‖(1 : ℝ)‖ := by simp