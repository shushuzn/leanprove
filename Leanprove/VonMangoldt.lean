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
  3. 素数幂部分: 证明收敛 (因为 ∑_p ∑_{k≥2} (log p)/p^k 收敛)
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

  Mathlib 文件: Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
  作者: Bhavik Mehta (2022)

  定义: vonMangoldt : ArithmeticFunction ℝ
  Λ(n) = if IsPrimePow n then Real.log(minFac n) else 0

  注: ArithmeticFunction ℝ 是从 ℕ 到 ℝ 的零保持函数 (f(0)=0)。
  Dirichlet 卷积: (f * g)(n) = ∑_{d|n} f(d) · g(n/d)
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
-- 证明: Λ(n) 是 n 的某个因子处的值, 而 ∑_{d|n} Λ(d) = Real.log n,
-- 所以单项 Λ(n) ≤ 总和 Real.log n
theorem vonMangoldt_le_log' (n : ℕ) :
    vonMangoldt n ≤ Real.log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log


/-!
  === 第二部分: Dirichlet 卷积关系 ===

  核心恒等式: ∑_{d|n} Λ(d) = Real.log n

  这等价于 Dirichlet 卷积 Λ * ζ = ArithmeticFunction.log,
  其中 ζ 是常值函数 1 (ζ(n) = 1 for n > 0),
  ArithmeticFunction.log 是算术函数 log(n) = Real.log(n)。

  通过 Möbius 反演: Λ = ArithmeticFunction.log * μ
  即 Λ(n) = -∑_{d|n} μ(d) · Real.log d
-/


-- 核心恒等式: ∑_{d|n} Λ(d) = Real.log n
-- 这是 von Mangoldt 函数最重要的性质
-- 证明使用 recOnPrimeCoprime (对互素乘性的归纳)
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

  Chebyshev ψ 函数 (第二 Chebyshev 函数):
  ψ(x) = ∑_{0 < n ≤ x} Λ(n) = ∑_{n ∈ Ioc 0 ⌊x⌋} Λ(n)

  Mathlib 定义: Chebyshev.psi (x : ℝ) : ℝ
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

  Mathlib 中已证明的关键界:
  - θ(x) ≤ Real.log(4) · x               (theta_le_log4_mul_x)
  - ψ(x) ≤ (Real.log(4) + 4) · x         (psi_le_const_mul_self)
  - |ψ(x) - θ(x)| ≤ 2√x · Real.log(x)   (abs_psi_sub_theta_le_sqrt_mul_log)
  - ψ(x) - θ(x) ≤ 2√x · Real.log(x)     (psi_sub_theta_le)

  这些界在 Mertens 定理的证明中起核心作用。
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

  核心结果: ∑_{n≤x} Λ(n)/n = Real.log x + O(1)

  证明策略:
  1. 用 Abel 求和公式将 ∑ Λ(n)/n 表达为 ψ 函数的积分形式
  2. 利用 Chebyshev 界 ψ(x) = O(x) 控制各项

  Abel 求和公式 (Mathlib: abelSummationProof.sum_mul_eq_sub_sub_integral_mul'):
  ∑_{k∈(n,m]} f(k)·c(k) = f(m)·∑_{k≤m} c(k) - f(n)·∑_{k≤n} c(k) - ∫_n^m f'(t)·∑_{k≤t} c(k) dt

  取 f(t) = 1/t, c(k) = Λ(k):
  ∑_{n≤x} Λ(n)/n = ψ(x)/x + ∫₁ˣ ψ(t)/t² dt

  要证明这等于 Real.log x + O(1), 需要:
  1. ψ(x)/x = O(1) ✓ (Chebyshev)
  2. ∫₁ˣ ψ(t)/t² dt - Real.log x = O(1) ← 这是关键难点

  注: 第 2 点等价于 ∫₁^∞ (ψ(t) - t)/t² dt 收敛。
  这可以用初等方法证明 (不依赖 PNT), 但在 Mathlib 中尚未形式化。
-/


/-- Abel 求和恒等式: 将 ∑_{n≤x} Λ(n)/n 用 ψ 表达 -/
theorem mertens_abel_identity (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) =
      ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
  sorry


/-- 关键引理: ∫₁ˣ ψ(t)/t² dt - Real.log x = O(1)
    这需要比 Chebyshev 界更精细的分析。
    等价于证明 ∫₁^∞ (ψ(t) - t)/t² dt 收敛。 -/
theorem psi_integral_sub_log_isBigO :
    (fun x : ℝ ↦ ∫ t in Set.Ioc 1 x, ψ t / (t * t) - Real.log x)
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry


/-!
  === 第六部分: 素数幂贡献 ===

  素数幂 (k ≥ 2) 对 ∑ Λ(n)/n 的贡献:
  ∑_{p^k ≤ x, k≥2} (Real.log p)/p^k

  这个和收敛, 因为:
  ∑_p ∑_{k≥2} (Real.log p)/p^k = ∑_p (Real.log p) / (p(p-1))
  而 ∑_p (Real.log p)/(p(p-1)) 收敛 (因为 (Real.log p)/(p(p-1)) ~ (Real.log p)/p²,
  且 ∑ 1/p^{1+ε} 收敛对 ε > 0)。

  Mathlib 已有: Nat.Primes.summable_rpow, 即 ∑ p^r 收敛 ↔ r < -1。
-/


/-- 素数幂 (k ≥ 2) 的 Λ 贡献是有界的 -/
theorem primePower_contribution_bounded :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬n.Prime,
        (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C := by
  sorry


/-!
  === 第七部分: Mertens 第一定理 ===

  Mertens 第一定理 (von Mangoldt 版本):
  ∑_{n≤x} Λ(n)/n = Real.log x + O(1)

  即函数 x ↦ ∑_{n≤x} Λ(n)/n - Real.log x 在 atTop 下有界。

  证明: 由 Abel 恒等式和关键引理直接推出。
-/


/-- **Mertens 第一定理** (von Mangoldt 版本)

    ∑_{n≤x} Λ(n)/n = Real.log x + O(1)

    即: 存在常数 C 使得 |∑_{n≤x} Λ(n)/n - Real.log x| ≤ C 对所有充分大的 x 成立。

    参考:
    - Hardy & Wright, "An Introduction to the Theory of Numbers", Theorem 425
    - Apostol, "Introduction to Analytic Number Theory", Theorem 4.12
-/
theorem mertens_first_theorem :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x)
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry


/-!
  === 第八部分: 推论和等价形式 ===

  Mertens 第一定理的几种等价表述:
  1. ∑_{n≤x} Λ(n)/n = Real.log x + O(1)          (von Mangoldt 版本)
  2. ∑_{p≤x} (Real.log p)/p = Real.log x + O(1)  (素数版本)
  3. ∑_{n≤x} Λ(n)/n - Real.log x 有界             (有界差版本)
-/


/-- Mertens 第一定理 (有界差版本): 存在常数使得差有界 -/
theorem mertens_first_theorem_bounded :
    ∃ C : ℝ, ∀ᶠ x in atTop,
      |∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x| ≤ C := by
  sorry


/-!
  === 第九部分: 与素数倒数和的联系 ===

  Mathlib 已证: Σ_{p} 1/p 发散 (Nat.Primes.not_summable_one_div)

  Mertens 第一定理给出了加权的素数倒数和:
  ∑_{p≤x} (Real.log p)/p = Real.log x + O(1)

  这与 ∑ 1/p 的发散性一致:
  如果 ∑_{p≤x} (Real.log p)/p ~ Real.log x, 那么 ∑_{p≤x} 1/p ~ Real.log (Real.log x)
  (由 Abel 求和 ∑ 1/p = ∑ (Real.log p)/p · 1/(Real.log p), 再 Abel 求和一次)

  Mertens 第二定理 (更精确):
  ∑_{p≤x} 1/p = Real.log (Real.log x) + M + O(1/Real.log x)
  其中 M 是 Meissel-Mertens 常数 ≈ 0.261497

  Mertens 第三定理:
  ∏_{p≤x} (1 - 1/p) ~ e^{-γ} / Real.log x
  其中 γ 是 Euler-Mascheroni 常数
-/


/-!
  === 第十部分: 总结和展望 ===

  本文件总结了 Mathlib 中 Von Mangoldt 函数的完整 API:

  已形式化 (直接来自 Mathlib):
  - Λ 的定义和基本性质 (apply, nonneg, prime, pow)
  - 核心恒等式 ∑_{d|n} Λ(d) = Real.log n
  - Dirichlet 卷积关系 Λ * ζ = ArithmeticFunction.log, Λ = ArithmeticFunction.log * μ
  - Λ(n) ≤ Real.log n 的上界
  - 与 ψ 函数的联系

  新增结果 (部分 sorry):
  - Abel 求和恒等式
  - Mertens 第一定理 ∑ Λ(n)/n = Real.log x + O(1)
  - 素数幂贡献的有界性

  待完成:
  - Abel 求和恒等式的完整证明 (需要可微性和可积性验证)
  - 关键积分引理 ∫₁ˣ (ψ(t)-t)/t² dt = O(1) 的证明
  - 素数幂贡献的显式界
  - Mertens 第二定理: ∑_{p≤x} 1/p = Real.log (Real.log x) + M + o(1)
  - Mertens 第三定理: ∏_{p≤x} (1-1/p) ~ e^{-γ}/Real.log x
-/
