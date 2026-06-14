/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- 素数倒数和的发散性
-- 基于 Mathlib.NumberTheory.SumPrimeReciprocals (Michael Stoll)
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
  == 素数倒数和的发散性 ==

  经典定理: Σ_{p素数} 1/p = ∞

  这是数论中最著名的结果之一，最早由欧拉证明。
  它说明素数虽然稀疏，但其倒数和仍然发散。

  证明方法 (Michael Stoll, 基于 Erdős):
  基于光滑数/粗糙数的划分，利用计数矛盾证明。
-/


-- 核心定理: 素数倒数级数不收敛
-- Σ_{p∈Nat.Primes} 1/p 不收敛
/-- 素数倒数级数 Σ 1/p 发散 -/
theorem not_summable_prime_reciprocal :
    ¬ Summable (fun p : Nat.Primes ↦ (1 : ℝ) / p) :=
  Nat.Primes.not_summable_one_div


/-!
  === 收敛性判据 (Nat.Primes.summable_rpow) ===

  Summable (fun p : Nat.Primes ↦ p^r) ↔ r < -1

  特别地:
  - r = -1:  Σ 1/p     不收敛 (素数倒数和发散)
  - r = -2:  Σ 1/p²    收敛
  - r = -3:  Σ 1/p³    收敛
  - r = 0:   Σ 1       不收敛 (素数无穷多)
-/
