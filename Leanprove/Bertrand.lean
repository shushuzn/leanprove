/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- Bertrand 假设 (Mathlib 已证明)
-- Mathlib.NumberTheory.Bertrand 包含完整证明

import Leanprove.Basic
import Mathlib.NumberTheory.Bertrand

/-!
  Bertrand 假设 (Mathlib 已证明)

  Nat.exists_prime_lt_and_le_two_mul:
    对所有 n ≠ 0，存在素数 p 满足 n < p ≤ 2n

  证明方法: Erdős 方法 (Proofs from THE BOOK)
  - 分析中心二项式系数 C(2n, n) 的素因子分解
  - 上界: C(2n, n) ≤ 4^n / sqrt(πn)
  - 下界: C(2n, n) ≥ 4^n / (2n)
  - (n, 2n] 中素数的乘积整除 C(2n, n)
  - 若不存在素数则导出矛盾

  参考文献:
  - Aigner & Ziegler, Proofs from THE BOOK
  - Tochiori, Considering the Proof of Bertrand's Postulate
  - Carneiro, Arithmetic in Metamath
-/

-- 应用1: 素数计数函数的下界
-- π(2n) - π(n) ≥ 1 对所有 n ≥ 1
/-- 素数计数间隙: (n, 2n] 中至少存在一个素数 -/
theorem prime_counting_gap (n : Nat) (hn : n ≠ 0) :
    ∃ p : Nat, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn

-- 应用2: 素数序列的密度
-- 对任意 n ≥ 1，区间 [n, 2n] 至少包含一个素数
/-- 区间 [n, 2n] 包含素数（Bertrand 等价形式）-/
theorem interval_contains_prime (n : Nat) (hn : n ≠ 0) :
    ∃ p : Nat, Nat.Prime p ∧ p ≥ n + 1 ∧ p ≤ 2 * n := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact ⟨p, hp, Nat.succ_le_of_lt hlt, hle⟩

-- 应用3: 素数间隙有界
-- 存在无穷多对不同的素数 (p, q) 满足 p < q ≤ 2p
/-- 存在无穷多对素数 (p,q) 满足 p < q ≤ 2p -/
theorem infinite_prime_pairs :
    ∀ N : Nat, ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧
    p > N ∧ p ≠ q ∧ q ≤ 2 * p := by
  intro N
  -- 第一步: 用 Bertrand 假设找 p > N
  have hN : N + 1 ≠ 0 := Nat.succ_ne_zero N
  obtain ⟨p, hp_prime, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (N + 1) hN
  have hp_gt : p > N := Nat.lt_of_succ_lt hlt
  -- 第二步: 再用 Bertrand 假设找 q ∈ (p, 2p]
  have hp_ne0 : p ≠ 0 := Nat.Prime.ne_zero hp_prime
  obtain ⟨q, hq_prime, hq_lt, hq_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul p hp_ne0
  -- p < q 确保 p ≠ q
  have hpq : p ≠ q := by omega
  exact ⟨p, q, hp_prime, hq_prime, hp_gt, hpq, hq_le⟩


-- 应用4: 素数有无穷多个
-- 经典结论: 不存在最大的素数
/-- 素数无穷（Bertrand 假设推论）-/
theorem infinite_primes : ∀ N : Nat, ∃ p : Nat, Nat.Prime p ∧ p > N := by
  intro N
  have hN : N + 1 ≠ 0 := Nat.succ_ne_zero N
  obtain ⟨p, hp, hlt, _hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N + 1) hN
  have hp_gt : N < p := Nat.lt_of_succ_lt hlt
  exact ⟨p, hp, hp_gt⟩


-- 应用5: 相邻素数的比值有界
-- 对任意素数 p ≥ 2，存在素数 q > p 使得 q ≤ 2p
-- 即 p_{k+1} / p_k ≤ 2
/-- 相邻素数比值有界: p_{k+1}/p_k ≤ 2 -/
theorem prime_ratio_bounded (p : Nat) (hp : Nat.Prime p) :
    ∃ q : Nat, Nat.Prime q ∧ q > p ∧ q ≤ 2 * p := by
  have hne : p ≠ 0 := Nat.Prime.ne_zero hp
  obtain ⟨q, hq, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul p hne
  exact ⟨q, hq, hlt, hle⟩


-- 应用6: Bertrand 假设的迭代应用
-- 对任意 n ≥ 1，区间 [n, 2n] 中至少有一个素数
/-- Bertrand 假设（迭代形式）-/
theorem bertrand_interval (n : Nat) (hn : 1 ≤ n) :
    ∃ p : Nat, Nat.Prime p ∧ n ≤ p ∧ p ≤ 2 * n := by
  have hne : n ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n hne
  exact ⟨p, hp, Nat.le_of_succ_le (Nat.succ_le_of_lt hlt), hle⟩
