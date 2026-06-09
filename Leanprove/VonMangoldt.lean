-- Von Mangoldt 函数与 Mertens 第一定理
-- 基于 Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev

/-!
  == Von Mangoldt 函数与 Mertens 第一定理 ==

  Von Mangoldt 函数 Λ(n) 的定义:
  - Λ(n) = log p  如果 n = p^k 对某素数 p 和正整数 k
  - Λ(n) = 0      否则

  核心恒等式: ∑_{d|n} Λ(d) = log n
  即 Λ * ζ = log (Dirichlet 卷积)

  Mertens 第一定理:
  ∑_{n≤x} Λ(n)/n = log x + O(1)

  证明策略:
  1. 将 ∑ Λ(n)/n 分解为素数部分 ∑ (log p)/p 和素数幂部分 ∑_{k≥2} (log p)/p^k
  2. 素数部分: 用 Abel 求和和 θ(x) = O(x) 得到 ∑ (log p)/p = log x + O(1)
  3. 素数幂部分: 证明收敛
  4. 合并两部分得到最终结果
-/

open ArithmeticFunction (vonMangoldt vonMangoldt_apply_one vonMangoldt_nonneg
  vonMangoldt_apply_prime vonMangoldt_apply_pow vonMangoldt_ne_zero_iff
  vonMangoldt_pos_iff vonMangoldt_eq_zero_iff vonMangoldt_sum
  vonMangoldt_mul_zeta zeta_mul_vonMangoldt log_mul_moebius_eq_vonMangoldt
  moebius_mul_log_eq_vonMangoldt sum_moebius_mul_log_eq)
open Asymptotics
open Filter

-- Local notation for Chebyshev functions
local notation "ψ" => Chebyshev.psi
local notation "θ" => Chebyshev.theta


/-!
  === 第一部分: Von Mangoldt 函数的基本性质 ===
-/

-- Λ(1) = 0 (因为 1 不是素数幂)
theorem vonMangoldt_one : vonMangoldt 1 = 0 :=
  vonMangoldt_apply_one

-- Λ(n) ≥ 0 对所有 n
theorem vonMangoldt_nonneg' (n : ℕ) : 0 ≤ vonMangoldt n :=
  vonMangoldt_nonneg

-- Λ(p) = Real.log p 对素数 p
theorem vonMangoldt_prime (p : ℕ) (hp : p.Prime) :
    vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

-- Λ(n^k) = Λ(n) 对 k ≠ 0
theorem vonMangoldt_pow' (n k : ℕ) (hk : k ≠ 0) :
    vonMangoldt (n ^ k) = vonMangoldt n :=
  vonMangoldt_apply_pow hk

-- Λ(n) ≠ 0 ↔ n 是素数幂
theorem vonMangoldt_nonzero_iff (n : ℕ) :
    vonMangoldt n ≠ 0 ↔ IsPrimePow n :=
  vonMangoldt_ne_zero_iff

-- Λ(n) > 0 ↔ n 是素数幂
theorem vonMangoldt_pos_iff' (n : ℕ) :
    0 < vonMangoldt n ↔ IsPrimePow n :=
  vonMangoldt_pos_iff

-- Λ(n) = 0 ↔ n 不是素数幂
theorem vonMangoldt_zero_iff (n : ℕ) :
    vonMangoldt n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_eq_zero_iff

-- Λ(n) ≤ Real.log n (对所有 n)
theorem vonMangoldt_le_log' (n : ℕ) :
    vonMangoldt n ≤ Real.log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log


/-!
  === 第二部分: Dirichlet 卷积关系 ===
-/

-- 核心恒等式: ∑_{d|n} Λ(d) = Real.log n
theorem vonMangoldt_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, vonMangoldt d = Real.log (n : ℝ) :=
  vonMangoldt_sum

-- Dirichlet 卷积: Λ * ζ = ArithmeticFunction.log
theorem vonMangoldt_mul_zeta_eq_log :
    vonMangoldt * ↑(ArithmeticFunction.zeta) = ArithmeticFunction.log :=
  vonMangoldt_mul_zeta

-- Dirichlet 卷积: ζ * Λ = ArithmeticFunction.log (交换律)
theorem zeta_mul_vonMangoldt_eq_log :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vonMangoldt =
      ArithmeticFunction.log :=
  zeta_mul_vonMangoldt

-- Möbius 反演: ArithmeticFunction.log * μ = Λ
theorem log_mul_moebius_eq_vonMangoldt' :
    ArithmeticFunction.log * ↑(ArithmeticFunction.moebius) = vonMangoldt :=
  log_mul_moebius_eq_vonMangoldt

-- Möbius 反演: μ * ArithmeticFunction.log = Λ (交换律)
theorem moebius_mul_log_eq_vonMangoldt' :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log =
      vonMangoldt :=
  moebius_mul_log_eq_vonMangoldt

-- 具体展开: -∑_{d|n} μ(d) · Real.log d = Λ(n)
theorem sum_moebius_mul_log_eq_vonMangoldt' (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
      -vonMangoldt n :=
  sum_moebius_mul_log_eq


/-!
  === 第三部分: 与 Chebyshev ψ 函数的联系 ===
-/

-- ψ(x) 也可以写成 Icc 求和 (因为 Λ(0) = 0)
theorem psi_eq_sum_vonMangoldt_Icc (x : ℝ) :
    ψ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n :=
  Chebyshev.psi_eq_sum_Icc x

-- 当 x 为自然数时, ψ(n) = ∑_{k=1}^{n} Λ(k)
theorem psi_nat_eq_sum (n : ℕ) :
    ψ (n : ℝ) = ∑ k ∈ Finset.Ioc 0 n, vonMangoldt k := by
  simp [Chebyshev.psi]

-- ψ(n) 的 Icc 版本 (包含 0, 但 Λ(0) = 0 所以无影响)
theorem psi_nat_eq_sum_Icc (n : ℕ) :
    ψ (n : ℝ) = ∑ k ∈ Finset.Icc 0 n, vonMangoldt k := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp

-- ∑_{k=1}^{n} Λ(k) = ψ(n)
theorem sum_vonMangoldt_eq_psi (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, vonMangoldt k = ψ (n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have : Finset.Icc 0 n = {0} ∪ Finset.Icc 1 n := by
    ext k; simp; omega
  rw [this, Finset.sum_union]
  · simp
  · simp


/-!
  === 第四部分: Chebyshev 界 ===
-/

-- ψ(x)/x 有界: |ψ(x)| ≤ (Real.log 4 + 4) · x
theorem psi_bounded (x : ℝ) (hx : 0 ≤ x) :
    |ψ x| ≤ (Real.log 4 + 4) * x := by
  rw [abs_of_nonneg (Chebyshev.psi_nonneg x)]
  exact Chebyshev.psi_le_const_mul_self hx

-- ψ(x) - θ(x) 的显式上界 (x ≥ 1)
theorem psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) :
    ψ x - θ x ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.psi_sub_theta_le hx

-- ψ(x) - θ(x) 的绝对值界 (x ≥ 1)
theorem abs_psi_sub_theta_le' (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx


/-!
  === 第五部分: Abel 求和与 Mertens 定理的关键引理 ===
-/

/-- Abel 求和恒等式: 将 ∑_{n≤x} Λ(n)/n 用 ψ 表达

    证明需要:
    1. Mathlib abelSummationProof.sum_mul_eq_sub_sub_integral_mul
    2. f(t) = 1/t 的可微性: deriv (fun t => 1/t) = fun t => -1/t²
    3. 可积性: IntegrableOn (fun t => -1/t²) (Set.Ioc 1 x)
    4. 应用 Abel 求和公式 with c = vonMangoldt, f = fun t => 1/t
-/
theorem mertens_abel_identity (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) =
      ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
  sorry


/-- 关键引理: ∫₁ˣ ψ(t)/t² dt - Real.log x = O(1)

    证明策略:
    - ∫₁ˣ ψ(t)/t² dt - ln x = ∫₁ˣ (ψ(t) - t)/t² dt
    - 需要 ∫₁^∞ (ψ(t) - t)/t² dt 收敛
    - 由 Chebyshev 界 |ψ(t) - t| ≤ C·t/ln(t) 可得
    - 此界不依赖 PNT，可用初等方法证明
-/
theorem psi_integral_sub_log_isBigO :
    (fun x : ℝ ↦ ∫ t in Set.Ioc 1 x, ψ t / (t * t) - Real.log x)
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry


/-!
  === 第六部分: 素数幂贡献 ===
-/

/-- 素数幂 (k ≥ 2) 的 Λ 贡献是有界的

    证明策略:
    1. 对每个素数 p, ∑_{k≥2} (log p)/p^k = (log p)/(p(p-1))
    2. (log p)/(p(p-1)) ≤ 4·p^{-1.5} (对 p ≥ 2)
    3. ∑_p p^{-1.5} 收敛 (Nat.Primes.summable_rpow, r = -1.5)
    
    需要: 级数收敛性的比较判别法 (Summable.of_nonneg_of_le)
    以及几何级数公式 ∑_{k≥2} 1/p^k = 1/(p(p-1))
-/
theorem primePower_contribution_bounded :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬n.Prime,
        (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C := by
  sorry


/-!
  === 第七部分: Mertens 第一定理 ===
-/

/-- **Mertens 第一定理** (von Mangoldt 版本)

    ∑_{n≤x} Λ(n)/n = Real.log x + O(1)

    证明策略:
    1. 由 Abel 恒等式 (sorry 1): ∑ Λ(n)/n = ψ(x)/x + ∫₁ˣ ψ(t)/t² dt
    2. 由关键引理 (sorry 2): ∫₁ˣ ψ(t)/t² dt - ln x = O(1)
    3. 由 Chebyshev 界: ψ(x)/x = O(1)
    4. 合并: ∑ Λ(n)/n - ln x = ψ(x)/x + (∫₁ˣ ψ(t)/t² dt - ln x) = O(1)

    依赖: Abel 恒等式 (mertens_abel_identity) 和 积分收敛 (psi_integral_sub_log_isBigO)
-/
theorem mertens_first_theorem :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x)
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry


/-!
  === 第八部分: 推论和等价形式 ===
-/

/-- Mertens 第一定理 (有界差版本)

    证明策略: 由 mertens_first_theorem 直接推出
    依赖: mertens_first_theorem
-/
theorem mertens_first_theorem_bounded :
    ∃ C : ℝ, ∀ᶠ x in atTop,
      |∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x| ≤ C := by
  sorry


/-!
  === 第九部分: 与素数倒数和的联系 ===

  Mathlib 已证: Σ_{p} 1/p 发散 (Nat.Primes.not_summable_one_div)
-/


/-!
  === 第十部分: 总结和展望 ===
-/
