-- Von Mangoldt 函数与 Mertens 第一定理
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Topology.Algebra.InfiniteSum.Real
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

theorem psi_integral_sub_log_isBigO : (fun x : ℝ ↦ ∫ t in Set.Ioc 1 x, ψ t / (t * t) - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by sorry

/-! === 第七部分: Mertens 定理 (3定理) === -/

-- Mertens Abel 恒等式: Abel 求和公式应用于 von Mangoldt 函数
theorem mertens_abel_identity (x : ℝ) (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) =
    ψ x / x + ∫ t in Set.Ioc 2 x, ψ t / (t * t) := by
  sorry

-- Mertens 第一定理: ∑_{p≤x} (log p)/p = log x + O(1)
theorem mertens_first_theorem :
    (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 ⌊x⌋₊), Real.log ↑p / ↑p - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry

-- Mertens 第一定理 (有界形式): |∑_{p≤x} (log p)/p - log x| ≤ C
theorem mertens_first_theorem_bounded :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 ⌊x⌋₊), Real.log ↑p / ↑p - Real.log x| ≤ C := by
  sorry
