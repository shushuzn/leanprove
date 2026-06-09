-- 等差数列中素数的特殊情形 (Special cases of Dirichlet's theorem)
-- 阶段3的初步成果: p ≡ 1 (mod 4) 和 p ≡ 3 (mod 4) 的素数无穷性
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.PrimesCongruentOne
import Leanprove.Basic

/-!
  == 等差数列中的素数: 特殊情形 ==

  Dirichlet 定理 (1837): 对任意 gcd(a,d) = 1, 等差数列 a, a+d, a+2d, ... 包含无穷多个素数。

  Mathlib 中已有完整 Dirichlet 定理 (Mathlib.NumberTheory.LSeries.PrimesInAP):
    Nat.forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
      ∃ p > n, p.Prime ∧ p ≡ a [MOD q]

  本文件:
  1. 用 Mathlib 现有定理直接导出 p ≡ 1 (mod 4) 的情形
  2. 用初等方法 (欧几里得式构造) 给出 p ≡ 3 (mod 4) 的原创证明
  3. 这两个结果的组合展示了 Dirichlet 定理在特殊模数下的两个面

  意义:
  - p ≡ 1 (mod 4) 的证明 (Mathlib) 使用分圆多项式, 是非初等的方法
  - p ≡ 3 (mod 4) 的证明 (本文件) 使用欧几里得式构造, 是初等方法
  - 两者互补, 体现了数论中不同同余类的不同证明策略
-/

open scoped Nat.Prime


/-!
  === Part 1: p ≡ 1 (mod 4) 有无穷多个素数 ===

  利用 Mathlib 的 Nat.exists_prime_gt_modEq_one:
    对任意 k ≠ 0 和 N, 存在素数 p > N 使得 p ≡ 1 (mod k)。
  取 k = 4 即得所需结果。

  Mathlib 的证明使用分圆多项式 Φ_k(b) 的性质:
  令 b = k·(N!), 则 Φ_k(b) 有素因子 p > N, 且 p ≡ 1 (mod k)。
  这是非初等的代数方法, 与 Dirichlet 的原始证明思路一致。
-/

-- 定理: 对任意 N, 存在素数 p > N 使得 p ≡ 1 (mod 4)
theorem exists_prime_mod_four_eq_one_gt (N : ℕ) :
    ∃ p, Nat.Prime p ∧ p > N ∧ p % 4 = 1 := by
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := Nat.exists_prime_gt_modEq_one N (by decide : 4 ≠ 0)
  -- hp_mod : p ≡ 1 [MOD 4], 即 p % 4 = 1 % 4 = 1
  have hp_mod4 : p % 4 = 1 := by
    rw [Nat.modEq_iff_dvd] at hp_mod
    omega
  exact ⟨p, hp_prime, hp_gt, hp_mod4⟩


-- 定理: p ≡ 1 (mod 4) 的素数有无穷多个
theorem infinite_primes_mod_four_eq_one :
    ∀ N, ∃ p, Nat.Prime p ∧ p > N ∧ p % 4 = 1 :=
  exists_prime_mod_four_eq_one_gt


/-!
  === Part 2: 辅助引理 — ≡ 3 (mod 4) 的数的素因子 ===

  核心观察: 若 n ≡ 3 (mod 4), 则 n 的素因子不可能全部 ≡ 1 (mod 4)
  (因为 1 × 1 × ... × 1 = 1, 不可能是 3)。且 2 不能整除奇数 n。
  所以至少有一个素因子 ≡ 3 (mod 4)。

  证明使用 Nat.primeFactorsList (Mathlib.Data.Nat.Factors):
  n 的素因子列表 (含重数), 其乘积等于 n。
-/

-- 辅助: 若列表中所有元素 ≡ 1 (mod 4), 则乘积 ≡ 1 (mod 4)
private theorem list_prod_mod_four_eq_one : ∀ {l : List ℕ},
    (∀ p ∈ l, p % 4 = 1) → l.prod % 4 = 1
  | [], _ => by simp [List.prod_nil, Nat.one_mod]
  | a :: l, h => by
    have ha : a % 4 = 1 := h a (by simp)
    have hl : ∀ p ∈ l, p % 4 = 1 := fun p hp => h p (by simp [hp])
    have ih : l.prod % 4 = 1 := list_prod_mod_four_eq_one hl
    simp only [List.prod_cons, Nat.mul_mod, ha, ih, Nat.one_mul]


-- 引理: ≡ 3 (mod 4) 的自然数必有 ≡ 3 (mod 4) 的素因子
theorem exists_prime_factor_mod_four_eq_three (n : ℕ) (hn : n % 4 = 3) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  -- n ≡ 3 (mod 4) → n ≥ 3, 所以 n ≠ 0
  have hn_pos : n ≠ 0 := by omega
  -- 素因子分解: primeFactorsList n 的乘积等于 n
  let pf := Nat.primeFactorsList n
  have hprod : pf.prod = n := Nat.prod_primeFactorsList hn_pos
  have hprime : ∀ p ∈ pf, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactorsList hp
  -- 反证: 假设不存在 ≡ 3 (mod 4) 的素因子
  by_contra hnone
  -- push_neg 已弃用, 用 push Not 替代; 或直接手动展开
  -- hnone : ¬∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3
  -- 展开后: ∀ p, Nat.Prime p → p ∣ n → p % 4 ≠ 3
  have hnone' : ∀ p, Nat.Prime p → p ∣ n → p % 4 ≠ 3 := by
    intro p hp_prime hp_dvd hp_mod4
    exact hnone ⟨p, hp_prime, hp_dvd, hp_mod4⟩
  -- 则所有素因子 ≡ 1 (mod 4)
  have hall_one : ∀ p ∈ pf, p % 4 = 1 := by
    intro p hp
    have hp_prime : Nat.Prime p := hprime p hp
    have hp_dvd : p ∣ n := by
      have : p ∣ pf.prod := List.dvd_prod hp
      rwa [hprod] at this
    -- 2 不能整除 n (n % 4 = 3 → n 是奇数)
    have hp_ne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hp_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
      omega
    -- p 是奇素数 → p % 4 ∈ {1, 3}
    have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by
      have : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left hp_ne2
      have : p % 4 < 4 := Nat.mod_lt p (by decide)
      omega
    -- 由 hnone: p 不满足 (Prime p ∧ p ∣ n ∧ p % 4 = 3)
    have hp_not3 : ¬(p % 4 = 3) := fun h3 => hnone' p hp_prime hp_dvd h3
    cases hmod4 with
    | inl h1 => exact h1
    | inr h3 => exfalso; exact hp_not3 h3
  -- 所有素因子 ≡ 1 (mod 4) → 乘积 ≡ 1 (mod 4)
  have hprod_mod : pf.prod % 4 = 1 := list_prod_mod_four_eq_one hall_one
  -- 但乘积 = n, 且 n ≡ 3 (mod 4), 矛盾!
  rw [hprod] at hprod_mod
  omega


/-!
  === Part 3: p ≡ 3 (mod 4) 有无穷多个素数 ===

  证明 (欧几里得式构造):
  给定任意 N, 令 S = {素数 p ≤ N : p ≡ 3 (mod 4)}, P = ∏_{p ∈ S} p。
  (若 S 为空, P = 1。)
  令 M = 4P - 1。
  - M ≡ 3 (mod 4)
  - M ≥ 3 (因为 P ≥ 1 → 4P ≥ 4 → M ≥ 3)
  由引理, M 有素因子 q ≡ 3 (mod 4)。
  若 q ≤ N, 则 q ∈ S, 所以 q ∣ P, 从而 q ∣ 4P。
  但 q ∣ (4P - 1), 所以 q ∣ 1, 矛盾。
  因此 q > N。
-/

-- 定理: 对任意 N, 存在素数 p > N 使得 p ≡ 3 (mod 4)
theorem exists_prime_mod_four_eq_three_gt (N : ℕ) :
    ∃ p, Nat.Prime p ∧ p > N ∧ p % 4 = 3 := by
  -- 构造: 收集所有 ≤ N 的 ≡ 3 (mod 4) 素数
  let S := (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p % 4 = 3)
  let P := S.prod id
  -- 令 M = 4P - 1
  let M := 4 * P - 1
  -- P ≥ 1 (空乘积为 1)
  have hP_pos : P ≥ 1 := by
    apply Finset.one_le_prod'
    intro x hx
    -- hx : x ∈ S = filter (fun p => Prime p ∧ p % 4 = 3) (range (N+1))
    have hx_mem : x ∈ Finset.filter (fun p => Nat.Prime p ∧ p % 4 = 3) (Finset.range (N + 1)) := by
      dsimp [S] at hx; exact hx
    have : x ∈ Finset.range (N + 1) := Finset.mem_of_mem_filter x hx_mem
    have : x < N + 1 := Finset.mem_range.1 this
    have hx_prime : Nat.Prime x := (Finset.mem_filter.1 hx_mem).2.1
    exact hx_prime.pos
  -- M ≡ 3 (mod 4)
  have hM_mod4 : M % 4 = 3 := by
    have : (4 * P) % 4 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_right 4 P)
    have h4P_ge : 4 * P ≥ 4 := by omega
    omega
  -- M ≥ 3
  have hM_ge : M ≥ 3 := by omega
  -- 由引理, M 有素因子 q ≡ 3 (mod 4)
  obtain ⟨q, hq_prime, hq_dvd, hq_mod4⟩ := exists_prime_factor_mod_four_eq_three M hM_mod4
  -- 证明 q > N
  have hq_gt : q > N := by
    by_contra hq_le
    have hq_le_N : q ≤ N := by omega
    -- q ≤ N 且 q 是素数且 q ≡ 3 (mod 4) → q ∈ S
    have hq_in_S : q ∈ S := by
      dsimp [S]
      refine Finset.mem_filter.2 ⟨?_, hq_prime, hq_mod4⟩
      exact Finset.mem_range.2 (by omega)
    -- q ∈ S → q ∣ P
    have hq_dvd_P : q ∣ P := Finset.dvd_prod_of_mem id hq_in_S
    -- q ∣ P → q ∣ 4P
    have hq_dvd_4P : q ∣ 4 * P := dvd_mul_of_dvd_right hq_dvd_P 4
    -- q ∣ 4P 且 q ∣ (4P - 1) → q ∣ 1
    have hq_dvd_one : q ∣ 1 := by
      dsimp [M] at hq_dvd
      have h4P_ge_1 : 4 * P ≥ 1 := by omega
      have hsub : q ∣ 4 * P - (4 * P - 1) := Nat.dvd_sub hq_dvd_4P hq_dvd
      -- 4*P - (4*P - 1) = 1
      have heq : 4 * P - (4 * P - 1) = 1 := by omega
      rwa [heq] at hsub
    -- 素数 q ≥ 2 不能整除 1
    have hq_ge2 : q ≥ 2 := hq_prime.two_le
    have : q ≤ 1 := Nat.le_of_dvd (by decide) hq_dvd_one
    omega
  exact ⟨q, hq_prime, hq_gt, hq_mod4⟩


-- 定理: p ≡ 3 (mod 4) 的素数有无穷多个
theorem infinite_primes_mod_four_eq_three :
    ∀ N, ∃ p, Nat.Prime p ∧ p > N ∧ p % 4 = 3 :=
  exists_prime_mod_four_eq_three_gt
