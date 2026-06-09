-- 等差数列中素数的特殊情形 (Special cases of Dirichlet's theorem)
-- 阶段3的初步成果: p ≡ 1 (mod 4) 和 p ≡ 3 (mod 4) 的素数无穷性
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Leanprove.Basic

/-!
  == 等差数列中的素数: 特殊情形 ==

  Dirichlet 定理 (1837): 对任意 gcd(a,d) = 1, 等差数列 a, a+d, a+2d, ... 包含无穷多个素数。

  Mathlib 中已有完整 Dirichlet 定理 (Mathlib.NumberTheory.LSeries.PrimesInAP):
    Nat.forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
      ∃ p > n, p.Prime ∧ p ≡ a [MOD q]

  本文件:
  1. 用 Mathlib 分圆多项式定理导出 p ≡ 1 (mod 4) 的情形 (代数方法)
  2. 用初等方法 (n² + 1 的素因子) 独立证明 p ≡ 1 (mod 4) 的无穷性
  3. 用欧几里得式构造给出 p ≡ 3 (mod 4) 的原创证明
  4. 用欧几里得式构造给出 p ≡ 5 (mod 6) 的证明

  意义:
  - p ≡ 1 (mod 4) 提供两种证明: 分圆多项式 (Mathlib) 与 n² + 1 素因子 (初等)
  - p ≡ 3 (mod 4) 使用欧几里得式构造 M = 4P - 1
  - p ≡ 5 (mod 6) 使用欧几里得式构造 M = 6P - 1
  - 三种方法互补, 体现数论中不同同余类的不同证明策略
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
  === Part 1B: p ≡ 1 (mod 4) 的初等证明 ===

  另一种独立的初等方法, 使用 n² + 1 的素因子性质:

  关键引理: 若奇素数 p 整除 n² + 1, 则 p ≡ 1 (mod 4)。
  这是因为 n² ≡ -1 (mod p), 即 -1 是模 p 的二次剩余,
  而 -1 是二次剩余当且仅当 p ≡ 1 (mod 4)。
  (由 ZMod.mod_four_ne_three_of_sq_eq_neg_one 导出)

  构造: 给定 N, 令 n = (N+1)!, M = n² + 1。
  M 的任何素因子 p 满足:
  - p ≠ 2 (M 是奇数)
  - p > N (否则 p ∣ n, 从而 p ∣ n², 又 p ∣ (n² + 1), 得 p ∣ 1, 矛盾)
  由引理 p ≡ 1 (mod 4)。

  与 Part 1 的分圆多项式方法完全独立, 是更初等的二次剩余论证。
-/

-- 引理: 若奇素数 p 整除 n² + 1, 则 p ≡ 1 (mod 4)
theorem prime_dvd_sq_add_one_mod_four (p n : ℕ) (hp : Nat.Prime p) (hp_ne2 : p ≠ 2)
    (hpdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  -- Step 1: 证明 n^2 % p = p - 1
  have hn2_mod : n ^ 2 % p = p - 1 := by
    have hmod : (n ^ 2 + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hpdvd
    -- (n^2 + 1) % p = (n^2 % p + 1 % p) % p by Nat.add_mod
    have h_add : (n ^ 2 + 1) % p = (n ^ 2 % p + 1 % p) % p := Nat.add_mod _ _ _
    rw [h_add] at hmod
    -- 1 % p = 1 since p > 1
    have h1mod : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
    rw [h1mod] at hmod
    -- Now hmod : (n^2 % p + 1) % p = 0
    have hp_gt1 : p > 1 := hp.one_lt
    by_cases heq : n ^ 2 % p = p - 1
    · exact heq
    · have hlt : n ^ 2 % p < p - 1 := by
        have : n ^ 2 % p < p := Nat.mod_lt _ hp.pos
        omega
      have : n ^ 2 % p + 1 < p := by omega
      have : (n ^ 2 % p + 1) % p = n ^ 2 % p + 1 := Nat.mod_eq_of_lt this
      rw [this] at hmod
      omega
  -- Step 2: 在 ZMod p 中, 设 a = (n : ZMod p), 证明 a^2 = -1
  have ha2_eq_neg1 : (n : ZMod p) ^ 2 = -1 := by
    -- Use val injectivity
    have hp_gt1 : 1 < p := hp.one_lt
    -- Compute ((n : ZMod p) ^ 2).val
    have h_pow_val : ((n : ZMod p) ^ 2).val = (n ^ 2) % p := by
      have h1 : ((n : ZMod p) ^ 2).val = ((n : ZMod p) * (n : ZMod p)).val := by
        rw [pow_two]
      rw [h1]
      have h2 : ((n : ZMod p) * (n : ZMod p)).val =
          ((n : ZMod p).val * (n : ZMod p).val) % p := ZMod.val_mul _ _
      rw [h2]
      have h3 : (n : ZMod p).val = n % p := ZMod.val_natCast _ _
      rw [h3]
      -- Goal: (n%p * n%p) % p = n^2 % p
      -- Use Nat.mul_mod (which says (a*b)%c = (a%c * b%c)%c) in reverse
      have h4 : (n % p * (n % p)) % p = (n * n) % p := by
        have h_step : (n * n) % p = (n % p * (n % p)) % p := by
          rw [Nat.mul_mod, Nat.mul_mod]
        exact h_step.symm
      rw [h4, ← Nat.pow_two]
    -- Compute (-1 : ZMod p).val = p - 1
    have h_neg1_val : (-1 : ZMod p).val = p - 1 := by
      cases p with
      | zero => contradiction
      | succ p' => exact ZMod.val_neg_one p'
    -- Show val(a^2) = val(-1)
    have h_val_eq : ((n : ZMod p) ^ 2).val = (-1 : ZMod p).val := by
      rw [h_pow_val, h_neg1_val]
      exact hn2_mod
    -- val injective → a^2 = -1
    exact ZMod.val_injective p h_val_eq
  -- Step 3: Apply ZMod.mod_four_ne_three_of_sq_eq_neg_one
  have hp_not3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one ha2_eq_neg1
  -- p is odd prime → p % 4 ∈ {1, 3}
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp_ne2
  have hp_mod4_cases : p % 4 = 1 ∨ p % 4 = 3 := by
    have : p % 4 < 4 := Nat.mod_lt p (by decide)
    omega
  cases hp_mod4_cases with
  | inl h1 => exact h1
  | inr h3 => exfalso; exact hp_not3 h3


-- 推论: n² + 1 的素因子只能是 2 或 ≡ 1 (mod 4)
theorem prime_factor_sq_add_one (p n : ℕ) (hp : Nat.Prime p)
    (hpdvd : p ∣ n ^ 2 + 1) : p = 2 ∨ p % 4 = 1 := by
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  · exact Or.inr (prime_dvd_sq_add_one_mod_four p n hp hp2 hpdvd)


/-!
  === Part 1C: p ≡ 1 (mod 4) 初等无穷性证明 ===

  使用 Part 1B 的引理, 构造性地证明: 对任意 N, 存在素数 p > N 且 p ≡ 1 (mod 4)。
  构造: n = (N+1)!, M = n² + 1。
  M 的素因子 p 满足 p > N 且 (p = 2 或 p ≡ 1 (mod 4))。
  由于 M 是奇数, p ≠ 2, 故 p ≡ 1 (mod 4)。
-/

-- 定理 (初等): 对任意 N, 存在素数 p > N 使得 p ≡ 1 (mod 4)
theorem exists_prime_mod_four_eq_one_gt_elementary (N : ℕ) :
    ∃ p, Nat.Prime p ∧ p > N ∧ p % 4 = 1 := by
  -- 对 N = 0, 直接给出 p = 5
  by_cases hN0 : N = 0
  · use 5
    constructor
    · decide
    · constructor
      · rw [hN0]; decide
      · decide
  -- N ≥ 1 的情形
  · have hN_pos : N ≥ 1 := by omega
    -- 构造: n = (N+1)!, M = n² + 1
    let n := (N + 1).factorial
    let M := n ^ 2 + 1
    -- M ≥ 2, 所以 M ≠ 1
    have hM_ge2 : M ≥ 2 := by
      have hn_ge1 : n ≥ 1 := Nat.factorial_pos (N + 1)
      have hn2_ge1 : n ^ 2 ≥ 1 := by
        have : n ^ 2 ≥ n := Nat.le_self_pow (by omega) n
        omega
      dsimp [M]
      omega
    have hM_ne1 : M ≠ 1 := by
      intro h
      have : M ≥ 2 := hM_ge2
      omega
    -- M 有素因子
    obtain ⟨p, hp_prime, hpM⟩ : ∃ p, Nat.Prime p ∧ p ∣ M := by
      exact Nat.exists_prime_and_dvd hM_ne1
    -- M 是奇数 (n = (N+1)! 是偶数因为 N ≥ 1, M = n² + 1 是奇数)
    have hM_odd : M % 2 = 1 := by
      have hn_even : n % 2 = 0 := by
        have h2pos : (2 : ℕ) > 0 := by decide
        have h2le : 2 ≤ N + 1 := by omega
        have : 2 ∣ (N + 1).factorial := Nat.dvd_factorial h2pos h2le
        exact Nat.mod_eq_zero_of_dvd this
      have hn2_even : (n ^ 2) % 2 = 0 := by
        rw [Nat.pow_two, Nat.mul_mod, hn_even]
      dsimp [M]
      have : (n ^ 2 + 1) % 2 = ((n ^ 2) % 2 + 1 % 2) % 2 := Nat.add_mod _ _ _
      rw [this, hn2_even]
    -- 取 M 的素因子 p, 由 Part 1B 知 p = 2 或 p ≡ 1 (mod 4)
    have hp_choice : p = 2 ∨ p % 4 = 1 := prime_factor_sq_add_one p n hp_prime hpM
    -- p ≠ 2 (M 是奇数, 2 不整除 M)
    have hp_ne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpM
      have : (2 : ℕ) ∣ M := hpM
      have hmod0 : M % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      have hmod1 : M % 2 = 1 := hM_odd
      omega
    -- 因此 p ≡ 1 (mod 4)
    have hp_mod4 : p % 4 = 1 := by
      cases hp_choice with
      | inl h2 => exfalso; exact hp_ne2 h2
      | inr h1 => exact h1
    -- 证明 p > N
    have hp_gt : p > N := by
      by_contra hp_le
      have hp_le_N : p ≤ N := by omega
      -- p ≤ N → p ∣ (N+1)! = n
      have hp_dvd_n : p ∣ n := by
        have hp_le_succ : p ≤ N + 1 := by omega
        exact Nat.dvd_factorial hp_prime.pos hp_le_succ
      -- p ∣ n → p ∣ n² (n² = n * n)
      have hp_dvd_n2 : p ∣ n ^ 2 := by
        have : n ^ 2 = n * n := by rw [Nat.pow_two]
        rw [this]
        exact dvd_mul_of_dvd_left hp_dvd_n n
      -- p ∣ n² 且 p ∣ (n² + 1) → p ∣ 1
      have hp_dvd_one : p ∣ 1 := by
        have hsub : p ∣ (n ^ 2 + 1) - n ^ 2 := Nat.dvd_sub hpM hp_dvd_n2
        have heq : (n ^ 2 + 1) - n ^ 2 = 1 := by
          have : n ^ 2 + 1 ≥ n ^ 2 := Nat.le_add_right (n ^ 2) 1
          omega
        rwa [heq] at hsub
      -- 素数 p ≥ 2 不能整除 1
      have : p ≤ 1 := Nat.le_of_dvd (by decide) hp_dvd_one
      have : p ≥ 2 := hp_prime.two_le
      omega
    exact ⟨p, hp_prime, hp_gt, hp_mod4⟩


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
  -- hnone : ¬∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3
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


/-!
  === Part 5: p ≡ 5 (mod 6) 有无穷多个素数 ===

  证明策略与 p ≡ 3 (mod 4) 完全平行:

  引理: 若 n ≡ 5 (mod 6), 则 n 必有 ≡ 5 (mod 6) 的素因子。
  (2 和 3 不整除 n; 大于 3 的素数 ≡ 1 或 5 (mod 6);
   全 ≡ 1 的乘积 ≡ 1, 不可能等于 5。)

  构造: 给定 N, 令 S = {素数 p ≤ N : p ≡ 5 (mod 6)}, P = ∏S, M = 6P - 1。
  M ≡ 5 (mod 6), M 有素因子 q ≡ 5 (mod 6), q > N (否则 q ∣ P → q ∣ 6P → q ∣ 1)。
-/

-- 辅助: 若列表中所有元素 ≡ 1 (mod 6), 则乘积 ≡ 1 (mod 6)
private theorem list_prod_mod_six_eq_one : ∀ {l : List ℕ},
    (∀ p ∈ l, p % 6 = 1) → l.prod % 6 = 1
  | [], _ => by simp [List.prod_nil, Nat.one_mod]
  | a :: l, h => by
    have ha : a % 6 = 1 := h a (by simp)
    have hl : ∀ p ∈ l, p % 6 = 1 := fun p hp => h p (by simp [hp])
    have ih : l.prod % 6 = 1 := list_prod_mod_six_eq_one hl
    simp only [List.prod_cons, Nat.mul_mod, ha, ih, Nat.one_mul]


-- 引理: ≡ 5 (mod 6) 的自然数必有 ≡ 5 (mod 6) 的素因子
theorem exists_prime_factor_mod_six_eq_five (n : ℕ) (hn : n % 6 = 5) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 6 = 5 := by
  have hn_pos : n ≠ 0 := by omega
  let pf := Nat.primeFactorsList n
  have hprod : pf.prod = n := Nat.prod_primeFactorsList hn_pos
  have hprime : ∀ p ∈ pf, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactorsList hp
  by_contra hnone
  have hnone' : ∀ p, Nat.Prime p → p ∣ n → p % 6 ≠ 5 := by
    intro p hp_prime hp_dvd hp_mod6
    exact hnone ⟨p, hp_prime, hp_dvd, hp_mod6⟩
  -- 所有素因子 ≡ 1 (mod 6)
  have hall_one : ∀ p ∈ pf, p % 6 = 1 := by
    intro p hp
    have hp_prime : Nat.Prime p := hprime p hp
    have hp_dvd : p ∣ n := by
      have : p ∣ pf.prod := List.dvd_prod hp
      rwa [hprod] at this
    -- 2 不整除 n (n ≡ 5 mod 6 → n 是奇数)
    have hp_ne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hp_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
      omega
    -- 3 不整除 n (n ≡ 5 mod 6 → n % 3 = 2)
    have hp_ne3 : p ≠ 3 := by
      intro h3
      rw [h3] at hp_dvd
      have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
      omega
    -- p ≥ 5 素数 → p % 6 ∈ {1, 5}
    have hmod6 : p % 6 = 1 ∨ p % 6 = 5 := by
      have : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left hp_ne2
      have : p % 3 ≠ 0 := by
        intro h
        have : p = 3 := by
          have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
          have := Nat.Prime.eq_one_or_self_of_dvd hp_prime 3 h3dvd
          omega
        exact hp_ne3 this
      have : p % 6 < 6 := Nat.mod_lt p (by decide)
      omega
    have hp_not5 : ¬(p % 6 = 5) := fun h5 => hnone' p hp_prime hp_dvd h5
    cases hmod6 with
    | inl h1 => exact h1
    | inr h5 => exfalso; exact hp_not5 h5
  -- 所有素因子 ≡ 1 (mod 6) → 乘积 ≡ 1 (mod 6)
  have hprod_mod : pf.prod % 6 = 1 := list_prod_mod_six_eq_one hall_one
  rw [hprod] at hprod_mod
  omega


-- 定理: 对任意 N, 存在素数 p > N 使得 p ≡ 5 (mod 6)
theorem exists_prime_mod_six_eq_five_gt (N : ℕ) :
    ∃ p, Nat.Prime p ∧ p > N ∧ p % 6 = 5 := by
  let S := (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p % 6 = 5)
  let P := S.prod id
  let M := 6 * P - 1
  -- P ≥ 1
  have hP_pos : P ≥ 1 := by
    apply Finset.one_le_prod'
    intro x hx
    have hx_mem : x ∈ Finset.filter (fun p => Nat.Prime p ∧ p % 6 = 5) (Finset.range (N + 1)) := by
      dsimp [S] at hx; exact hx
    have : x ∈ Finset.range (N + 1) := Finset.mem_of_mem_filter x hx_mem
    have hx_prime : Nat.Prime x := (Finset.mem_filter.1 hx_mem).2.1
    exact hx_prime.pos
  -- M ≡ 5 (mod 6)
  have hM_mod6 : M % 6 = 5 := by
    have : (6 * P) % 6 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_right 6 P)
    have h6P_ge : 6 * P ≥ 6 := by omega
    omega
  -- M ≥ 5
  have hM_ge : M ≥ 5 := by omega
  -- M 有素因子 q ≡ 5 (mod 6)
  obtain ⟨q, hq_prime, hq_dvd, hq_mod6⟩ := exists_prime_factor_mod_six_eq_five M hM_mod6
  -- q > N
  have hq_gt : q > N := by
    by_contra hq_le
    have hq_le_N : q ≤ N := by omega
    have hq_in_S : q ∈ S := by
      dsimp [S]
      refine Finset.mem_filter.2 ⟨?_, hq_prime, hq_mod6⟩
      exact Finset.mem_range.2 (by omega)
    have hq_dvd_P : q ∣ P := Finset.dvd_prod_of_mem id hq_in_S
    have hq_dvd_6P : q ∣ 6 * P := dvd_mul_of_dvd_right hq_dvd_P 6
    have hq_dvd_one : q ∣ 1 := by
      dsimp [M] at hq_dvd
      have h6P_ge_1 : 6 * P ≥ 1 := by omega
      have hsub : q ∣ 6 * P - (6 * P - 1) := Nat.dvd_sub hq_dvd_6P hq_dvd
      have heq : 6 * P - (6 * P - 1) = 1 := by omega
      rwa [heq] at hsub
    have : q ≤ 1 := Nat.le_of_dvd (by decide) hq_dvd_one
    have : q ≥ 2 := hq_prime.two_le
    omega
  exact ⟨q, hq_prime, hq_gt, hq_mod6⟩


-- 定理: p ≡ 5 (mod 6) 的素数有无穷多个
theorem infinite_primes_mod_six_eq_five :
    ∀ N, ∃ p, Nat.Prime p ∧ p > N ∧ p % 6 = 5 :=
  exists_prime_mod_six_eq_five_gt
