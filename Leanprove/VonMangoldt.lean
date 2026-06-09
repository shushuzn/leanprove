-- Von Mangoldt 函数 (已完成定理)
-- 基于 Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev

/-!
  == Von Mangoldt 函数 ==

  Von Mangoldt 函数 Λ(n) 的定义:
  - Λ(n) = log p  如果 n = p^k 对某素数 p 和正整数 k
  - Λ(n) = 0      否则

  本文件包含已证明的定理 (共 17 个)。
  Mertens 第一定理需要实分析基础设施, 待日后完善。
-/

open ArithmeticFunction (vonMangoldt vonMangoldt_apply_one vonMangoldt_nonneg
  vonMangoldt_apply_prime vonMangoldt_apply_pow vonMangoldt_ne_zero_iff
  vonMangoldt_pos_iff vonMangoldt_eq_zero_iff vonMangoldt_sum
  vonMangoldt_mul_zeta zeta_mul_vonMangoldt log_mul_moebius_eq_vonMangoldt
  moebius_mul_log_eq_vonMangoldt sum_moebius_mul_log_eq)
open Asymptotics
open Filter

local notation "ψ" => Chebyshev.psi
local notation "θ" => Chebyshev.theta


/-!
  === 第一部分: Von Mangoldt 函数的基本性质 (8 theorem) ===
-/

theorem vonMangoldt_one : vonMangoldt 1 = 0 := vonMangoldt_apply_one

theorem vonMangoldt_nonneg' (n : ℕ) : 0 ≤ vonMangoldt n := vonMangoldt_nonneg

theorem vonMangoldt_prime (p : ℕ) (hp : p.Prime) : vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

theorem vonMangoldt_pow' (n k : ℕ) (hk : k ≠ 0) : vonMangoldt (n ^ k) = vonMangoldt n :=
  vonMangoldt_apply_pow hk

theorem vonMangoldt_nonzero_iff (n : ℕ) : vonMangoldt n ≠ 0 ↔ IsPrimePow n :=
  vonMangoldt_ne_zero_iff

theorem vonMangoldt_pos_iff' (n : ℕ) : 0 < vonMangoldt n ↔ IsPrimePow n := vonMangoldt_pos_iff

theorem vonMangoldt_zero_iff (n : ℕ) : vonMangoldt n = 0 ↔ ¬IsPrimePow n := vonMangoldt_eq_zero_iff

theorem vonMangoldt_le_log' (n : ℕ) : vonMangoldt n ≤ Real.log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log


/-!
  === 第二部分: Dirichlet 卷积关系 (6 theorem) ===
-/

theorem vonMangoldt_sum_divisors (n : ℕ) : ∑ d ∈ n.divisors, vonMangoldt d = Real.log (n : ℝ) :=
  vonMangoldt_sum

theorem vonMangoldt_mul_zeta_eq_log :
    vonMangoldt * ↑(ArithmeticFunction.zeta) = ArithmeticFunction.log := vonMangoldt_mul_zeta

theorem zeta_mul_vonMangoldt_eq_log :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vonMangoldt = ArithmeticFunction.log :=
  zeta_mul_vonMangoldt

theorem log_mul_moebius_eq_vonMangoldt' :
    ArithmeticFunction.log * ↑(ArithmeticFunction.moebius) = vonMangoldt :=
  log_mul_moebius_eq_vonMangoldt

theorem moebius_mul_log_eq_vonMangoldt' :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log = vonMangoldt :=
  moebius_mul_log_eq_vonMangoldt

theorem sum_moebius_mul_log_eq_vonMangoldt' (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) = -vonMangoldt n :=
  sum_moebius_mul_log_eq


/-!
  === 第三部分: Chebyshev 界 (3 theorem) ===
-/

theorem psi_bounded (x : ℝ) (hx : 0 ≤ x) : |ψ x| ≤ (Real.log 4 + 4) * x := by
  have h : ψ x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx
  have h_nonneg : 0 ≤ ψ x := Chebyshev.psi_nonneg x
  rw [abs_of_nonneg h_nonneg]
  exact h

theorem psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) : ψ x - θ x ≤ 2 * Real.sqrt x * Real.log x := by
  have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx
  have : ψ x - θ x ≤ |ψ x - θ x| := le_abs_self (ψ x - θ x)
  exact this.trans h

theorem abs_psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) : |ψ x - θ x| ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx
