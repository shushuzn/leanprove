/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- Uses Mathlib for Nat.Prime definition and related lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring.RingNF

/-!
  Helper: If p is prime and k is in the range (1, p), then p is not divisible by k.

  This bridges Mathlib's Nat.Prime (defined via divisibility) to the
  modular arithmetic formulation used throughout the proofs.
-/

/-- 素数 p 在范围内不整除 k -/ 
theorem prime_not_dvd_of_range {p : Nat} (hp : Nat.Prime p) (_hge : 5 ≤ p) {k : Nat}
    (hk1 : 1 < k) (hkp : k < p) : p % k ≠ 0 := by
  intro h
  have hk_dvd : k ∣ p := Nat.dvd_of_mod_eq_zero h
  have := hp.eq_one_or_self_of_dvd k hk_dvd
  omega


/-!
  Lemma: For any prime p >= 5, p ≡ 1 or 5 (mod 6).

  Proof strategy:
  - p is prime ≥ 5, so p is not divisible by 2 or 3.
  - p % 2 ≠ 0 means p is odd.
  - p % 3 ≠ 0 means p is not a multiple of 3.
  - The possible residues mod 6 are {0,1,2,3,4,5}.
  - Eliminating even residues (0,2,4) and multiples of 3 (0,3),
    only 1 and 5 remain.

  Examples:
    p = 5:  5 % 6 = 5  ✓
    p = 7:  7 % 6 = 1  ✓
    p = 11: 11 % 6 = 5  ✓
    p = 13: 13 % 6 = 1  ✓
-/

/-- 素数 p ≥ 5 模 6 余 1 或 5 -/
theorem prime_ge_five_mod_six (p : Nat) (hp : Nat.Prime p) (hge : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  -- p is not divisible by 2
  have h2 : p % 2 ≠ 0 := prime_not_dvd_of_range hp hge (by decide) (by omega)
  -- p is odd
  have hp_odd : p % 2 = 1 := by omega
  -- p is not divisible by 3
  have h3 : p % 3 ≠ 0 := prime_not_dvd_of_range hp hge (by decide) (by omega)
  -- Enumerate possible residues mod 6
  have : p % 6 < 6 := Nat.mod_lt p (by decide)
  have : p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by omega
  rcases this with (h1 | h2v | h3v | h4 | h5)
  · exact Or.inl h1
  · exfalso; omega   -- p % 6 = 2 implies p % 2 = 0
  · exfalso; omega   -- p % 6 = 3 implies p % 3 = 0
  · exfalso; omega   -- p % 6 = 4 implies p % 2 = 0
  · exact Or.inr h5


/-!
  Theorem: For any prime p >= 5, 24 divides p^2 - 1.

  Proof strategy (Chinese Remainder Theorem approach):
  - By prime_ge_five_mod_six, p ≡ 1 or 5 (mod 6).
  - From this, p % 3 ∈ {1, 2}, hence p^2 ≡ 1 (mod 3).
  - Separately, p is odd, so p % 8 ∈ {1, 3, 5, 7}, hence p^2 ≡ 1 (mod 8).
  - Since gcd(3, 8) = 1, we get p^2 ≡ 1 (mod 24), hence 24 ∣ p^2 - 1.

  This is a classical number theory result. For example:
    p = 5:  25 - 1 = 24  = 24 × 1  ✓
    p = 7:  49 - 1 = 48  = 24 × 2  ✓
    p = 11: 121 - 1 = 120 = 24 × 5  ✓
    p = 13: 169 - 1 = 168 = 24 × 7  ✓
-/

-- The main theorem: uses prime_ge_five_mod_six for the mod 3 analysis
/-- 素数 p ≥ 5 时 24 ∣ p² - 1 -/
theorem prime_ge_five_sq_sub_one_dvd (p : Nat) (hp : Nat.Prime p) (hge : 5 ≤ p) :
    24 ∣ p ^ 2 - 1 := by
  -- Rewrite p^2 as p * p for easier reasoning
  have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  rw [hp2]
  -- Step 1: By prime_ge_five_mod_six, p ≡ 1 or 5 (mod 6)
  have hmod6 : p % 6 = 1 ∨ p % 6 = 5 := prime_ge_five_mod_six p hp hge
  -- Step 2: Derive (p * p) ≡ 1 (mod 3) from the mod 6 result
  have hmod3 : (p * p) % 3 = 1 := by
    rcases hmod6 with (h6 | h6)
    · -- Case p % 6 = 1: then p % 3 = 1
      have hp3 : p % 3 = 1 := by
        have : p % 6 % 3 = 1 % 3 := by rw [h6]
        rw [Nat.mod_mod_of_dvd p (by decide : 3 ∣ 6)] at this
        exact this
      have h1 : (p * p) % 3 = (p % 3 * (p % 3)) % 3 := by rw [Nat.mul_mod]
      rw [h1, hp3]
    · -- Case p % 6 = 5: then p % 3 = 2
      have hp3 : p % 3 = 2 := by
        have : p % 6 % 3 = 5 % 3 := by rw [h6]
        rw [Nat.mod_mod_of_dvd p (by decide : 3 ∣ 6)] at this
        exact this
      have h1 : (p * p) % 3 = (p % 3 * (p % 3)) % 3 := by rw [Nat.mul_mod]
      rw [h1, hp3]
  -- Step 3: p is odd
  have hp_odd : p % 2 = 1 := by
    have : p % 2 ≠ 0 := prime_not_dvd_of_range hp hge (by decide) (by omega)
    omega
  -- Step 4: (p * p) ≡ 1 (mod 8): check all four odd residues mod 8
  have hmod8 : (p * p) % 8 = 1 := by
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases this with (h | h | h | h)
    · rw [Nat.mul_mod, h]   -- (1 * 1) % 8 = 1
    · rw [Nat.mul_mod, h]   -- (3 * 3) % 8 = 1
    · rw [Nat.mul_mod, h]   -- (5 * 5) % 8 = 1
    · rw [Nat.mul_mod, h]   -- (7 * 7) % 8 = 1
  -- Step 5: Chinese Remainder Theorem: combine mod 3 and mod 8 to get mod 24
  have hmod24 : (p * p) % 24 = 1 := by
    have hlt : (p * p) % 24 < 24 := Nat.mod_lt (p * p) (by decide)
    have h24_3 : (p * p) % 24 % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd (p * p) (by decide : 3 ∣ 24)]
      exact hmod3
    have h24_8 : (p * p) % 24 % 8 = 1 := by
      rw [Nat.mod_mod_of_dvd (p * p) (by decide : 8 ∣ 24)]
      exact hmod8
    omega
  -- p * p ≥ 1, so subtraction is valid
  have hpos : p * p ≥ 1 := by omega
  -- (p * p) % 24 = 1 implies 24 ∣ p * p - 1
  have hmod_sub : (p * p - 1) % 24 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hmod_sub


/-!
  Theorem: Consecutive integers are coprime, i.e., gcd(n, n+1) = 1.

  Proof strategy:
  - If d divides both n and n+1, then d divides (n+1) - n = 1.
  - The only positive divisor of 1 is 1 itself.
  - Therefore gcd(n, n+1) = 1.

  This is a fundamental result in number theory, kept as a standalone tool
  for future extensions (e.g., analyzing gcd(p-1, p+1) in the main theorem's context).
-/

-- Helper: any common divisor of consecutive integers must be 1
/-- 相邻自然数的公因子必为 1 -/
theorem dvd_consecutive_eq_one {d n : Nat} (hd : 0 < d)
    (h1 : d ∣ n) (h2 : d ∣ (n + 1)) : d = 1 := by
  have hsub : d ∣ (n + 1 - n) := Nat.dvd_sub h2 h1
  have heq : n + 1 - n = 1 := by omega
  rw [heq] at hsub
  have hle : d ≤ 1 := Nat.le_of_dvd (by decide) hsub
  omega

-- Main result: gcd of consecutive integers is 1
/-- 相邻自然数的最大公约数为 1 -/
theorem gcd_consecutive (n : Nat) : Nat.gcd n (n + 1) = 1 := by
  by_cases hn : n = 0
  · rw [hn]; decide
  · let d := Nat.gcd n (n + 1)
    have hd_pos : 0 < d := by
      have : 0 < n := by omega
      exact Nat.gcd_pos_of_pos_left (n + 1) this
    have hd1 : d ∣ n := (Nat.gcd_dvd n (n + 1)).1
    have hd2 : d ∣ (n + 1) := (Nat.gcd_dvd n (n + 1)).2
    exact dvd_consecutive_eq_one hd_pos hd1 hd2


/-!
  Theorem: For any two primes p, q >= 5, 24 divides p² - q².

  Proof strategy:
  - From the main theorem, 24 ∣ p² - 1 and 24 ∣ q² - 1.
  - p² - q² = (p² - 1) - (q² - 1).
  - Since 24 divides both, 24 divides their difference.

  Examples:
    p=7, q=5:   49 - 25 = 24  = 24 × 1  ✓
    p=11, q=7:  121 - 49 = 72 = 24 × 3  ✓
    p=13, q=5:  169 - 25 = 144 = 24 × 6  ✓
-/

-- Helper: 24 ∣ p*p - 1 (same content as prime_ge_five_sq_sub_one_dvd,
-- using p*p notation for use in prime_sq_diff_dvd_24)
/-- 平方差公式的整除版本 -/
theorem dvd_sq_sub_one (p : Nat) (hp : Nat.Prime p) (hge : 5 ≤ p) :
    24 ∣ p * p - 1 := by
  have h := prime_ge_five_sq_sub_one_dvd p hp hge
  -- p^2 = p*p by definition
  have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  have hpp : p ^ 2 - 1 = p * p - 1 := by rw [hp2]
  rw [← hpp]
  exact h

-- Helper: algebraic identity (a-1) - (b-1) = a - b
/-- 减法恒等式: (a-1) - (b-1) = a - b -/
theorem sub_one_sub_sub_one {a b : Nat} (hb1 : 1 ≤ b) (hba : b ≤ a) :
    (a - 1) - (b - 1) = a - b := by
  have h : a - 1 = (a - b) + (b - 1) := by
    have : a - b + b = a := Nat.sub_add_cancel hba
    have : a - b + (b - 1) = a - b + b - 1 := by
      rw [← Nat.add_sub_assoc hb1]
    omega
  rw [h]
  rw [Nat.add_sub_cancel]

-- Main result: 24 ∣ p² - q² for primes p, q ≥ 5
/-- 素数平方差整除 24（推广到两个素数）-/
theorem prime_sq_diff_dvd_24 (p q : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_ge : 5 ≤ p) (hq_ge : 5 ≤ q) :
    24 ∣ p * p - q * q := by
  -- Prove 1 ≤ q*q using Nat.mul_le_mul (omega cannot handle nonlinear arithmetic)
  have hq1 : 1 ≤ q := by omega
  have hpos_q : 1 ≤ q * q := by
    have : 1 * 1 ≤ q * q := Nat.mul_le_mul hq1 hq1
    simpa [Nat.one_mul] using this
  have hp1 : 1 ≤ p := by omega
  have hpos_p : 1 ≤ p * p := by
    have : 1 * 1 ≤ p * p := Nat.mul_le_mul hp1 hp1
    simpa [Nat.one_mul] using this
  -- Now introduce the divisibility hypotheses
  have hdp : 24 ∣ p * p - 1 := dvd_sq_sub_one p hp hp_ge
  have hdq : 24 ∣ q * q - 1 := dvd_sq_sub_one q hq hq_ge
  by_cases hpq : p * p ≥ q * q
  · -- Case: p² ≥ q²
    have hsub : 24 ∣ (p * p - 1) - (q * q - 1) := Nat.dvd_sub hdp hdq
    have heq : (p * p - 1) - (q * q - 1) = p * p - q * q :=
      sub_one_sub_sub_one hpos_q hpq
    rw [← heq]
    exact hsub
  · -- Case: p² < q², so p² - q² = 0 (truncated subtraction)
    have hzero : p * p - q * q = 0 := by
      have : p * p < q * q := by omega
      exact Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ (Nat.lt_succ_of_lt this))
    rw [hzero]
    -- 24 ∣ 0 because 0 = 24 * 0
    have hmod : 0 % 24 = 0 := by decide
    exact Nat.dvd_of_mod_eq_zero hmod


/-!
  === DEEP STRUCTURAL ANALYSIS ===

  The theorems above prove 24 ∣ p² - 1 using CRT (mod 3 × mod 8 → mod 24).
  The theorems below reveal the deeper algebraic structure.

  Key insight: p² - 1 = (p - 1)(p + 1) — a difference of squares.

  The three factors that produce 24 = 8 × 3:
  ① p odd → p-1, p+1 are consecutive even numbers → 8 ∣ (p-1)(p+1).
  ② p not div by 3 → 3 divides p-1 or p+1 → 3 ∣ (p-1)(p+1).
  ③ gcd(p-1, p+1) = 2 (proven via gcd_consecutive).

  This factorization explains WHY 24 appears: it is the product of
  the contributions from the prime 2 (giving factor 8) and the
  prime 3 (giving factor 3). The gcd result ③ shows these factors
  are "independent" — the overlap between p-1 and p+1 is exactly 2.
-/

-- Factorization: p² - 1 = (p-1)(p+1)
/-- 因式分解: p² - 1 = (p-1)(p+1) -/
theorem sq_sub_one_eq_mul_pm1 (p : Nat) (hp1 : 1 ≤ p) :
    p * p - 1 = (p - 1) * (p + 1) := by
  have hp2 : 1 ≤ p * p := by
    have : 1 * 1 ≤ p * p := Nat.mul_le_mul hp1 hp1
    simpa [Nat.one_mul] using this
  have hpp : p ≤ p * p := by
    have : p * 1 ≤ p * p := Nat.mul_le_mul (by omega) hp1
    simpa [Nat.mul_one] using this
  -- Expand (p-1)(p+1) step by step
  have h1 : (p - 1) * (p + 1) = (p - 1) * p + (p - 1) * 1 := by
    rw [Nat.mul_add]
  have h2 : (p - 1) * p + (p - 1) * 1 = (p - 1) * p + (p - 1) := by
    rw [Nat.mul_one]
  have h3 : (p - 1) * p = p * p - p := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul]
  -- Combine: (p-1)(p+1) = (p*p - p) + (p-1)
  have h4 : (p - 1) * (p + 1) = p * p - p + (p - 1) := by
    rw [h1, h2, h3]
  have h5 : p * p - p + (p - 1) = p * p - 1 := by
    have h5a : p * p - p + (p - 1) = p * p - p + p - 1 := by
      rw [← Nat.add_sub_assoc hp1]
    rw [h5a]
    have h5b : p * p - p + p = p * p := by
      rw [Nat.sub_add_cancel hpp]
    rw [h5b]
  -- Chain: (p-1)(p+1) = (p*p - p) + (p-1) = p*p - 1
  rw [h4, h5]


/-!
  gcd(p-1, p+1) = 2 for odd p ≥ 3.

  Proof:
  - d = gcd(p-1, p+1) divides (p+1)-(p-1) = 2, so d ≤ 2.
  - p odd → p-1 even, p+1 even → 2 ∣ gcd(p-1, p+1) → 2 ≤ d.
  - Therefore d = 2.

  This connects gcd_consecutive to the main theorem family:
  writing p-1 = 2k, p+1 = 2(k+1), we have
  gcd(p-1, p+1) = 2 · gcd(k, k+1) = 2 · 1 = 2,
  where gcd(k, k+1) = 1 is exactly gcd_consecutive.
-/

/-- 相邻两数的 gcd 为 2 -/
theorem gcd_pm1_eq_two (p : Nat) (hge : 3 ≤ p) (hodd : p % 2 = 1) :
    Nat.gcd (p - 1) (p + 1) = 2 := by
  have hp1_pos : 0 < p - 1 := by omega
  -- d = gcd(p-1, p+1) divides both
  have hdvd1 : Nat.gcd (p - 1) (p + 1) ∣ (p - 1) :=
    (Nat.gcd_dvd (p - 1) (p + 1)).1
  have hdvd2 : Nat.gcd (p - 1) (p + 1) ∣ (p + 1) :=
    (Nat.gcd_dvd (p - 1) (p + 1)).2
  -- d divides the difference (p+1) - (p-1) = 2
  have hdvd_diff : Nat.gcd (p - 1) (p + 1) ∣ (p + 1 - (p - 1)) :=
    Nat.dvd_sub hdvd2 hdvd1
  have hdiff : p + 1 - (p - 1) = 2 := by omega
  rw [hdiff] at hdvd_diff
  -- d ∣ 2 and d > 0 → d ≤ 2
  have hd_pos : 0 < Nat.gcd (p - 1) (p + 1) :=
    Nat.gcd_pos_of_pos_left (p + 1) hp1_pos
  have hle2 : Nat.gcd (p - 1) (p + 1) ≤ 2 :=
    Nat.le_of_dvd (by decide) hdvd_diff
  -- p is odd → p-1 and p+1 are both even → 2 ∣ gcd(p-1, p+1)
  have hp1_even : (p - 1) % 2 = 0 := by omega
  have h2_dvd_p1 : 2 ∣ (p - 1) := Nat.dvd_of_mod_eq_zero hp1_even
  have h2_dvd_p2 : 2 ∣ (p + 1) := by
    have : (p + 1) % 2 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  have h2_dvd_gcd : 2 ∣ Nat.gcd (p - 1) (p + 1) :=
    Nat.dvd_gcd h2_dvd_p1 h2_dvd_p2
  -- 2 ∣ d and d > 0 → 2 ≤ d
  have hge2 : 2 ≤ Nat.gcd (p - 1) (p + 1) :=
    Nat.le_of_dvd hd_pos h2_dvd_gcd
  -- 2 ≤ d ≤ 2 → d = 2
  omega


/-!
  Independent divisibility results for the factors of p² - 1 = (p-1)(p+1):

  ① 8 ∣ (p-1)(p+1) for any odd p ≥ 5.
     Reason: p-1 and p+1 are consecutive even numbers.
     One is 2 mod 4, the other is 0 mod 4. Product has factor 2 × 4 = 8.

  ② 3 ∣ (p-1)(p+1) when p is not divisible by 3.
     Reason: p-1, p, p+1 are three consecutive integers.
     Exactly one is divisible by 3. Since p isn't, 3 divides p-1 or p+1.

  Together with gcd(p-1, p+1) = 2, these explain the exact power of 2
  and 3 that divides p² - 1: the 2-contribution is exactly 8 (not 16),
  and the 3-contribution is exactly 3 (not 9), giving 8 × 3 = 24.
-/

-- 8 divides (p-1)(p+1) for any odd number p ≥ 3
/-- 奇数时 8 ∣ p² - 1 -/
theorem eight_dvd_sq_sub_one (p : Nat) (hge : 3 ≤ p) (hodd : p % 2 = 1) :
    8 ∣ (p - 1) * (p + 1) := by
  -- Case analysis on p mod 8
  have hcases : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨
                p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7 := by omega
  rcases hcases with (h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7)
  · omega   -- p % 8 = 0 contradicts p odd
  · -- p % 8 = 1: (p-1)(p+1) % 8 = 0*2 % 8 = 0
    have hmod : (p - 1) * (p + 1) % 8 = 0 := by
      have ha : (p - 1) % 8 = 0 := by omega
      have h1 : ((p - 1) * (p + 1)) % 8 = ((p - 1) % 8 * ((p + 1) % 8)) % 8 := by
        rw [Nat.mul_mod]
      rw [h1, ha, Nat.zero_mul, Nat.zero_mod]
    exact Nat.dvd_of_mod_eq_zero hmod
  · omega   -- p % 8 = 2 contradicts p odd
  · -- p % 8 = 3: (p-1)(p+1) % 8 = 2*4 % 8 = 0
    have hmod : (p - 1) * (p + 1) % 8 = 0 := by
      have ha : (p - 1) % 8 = 2 := by omega
      have hb : (p + 1) % 8 = 4 := by omega
      have h1 : ((p - 1) * (p + 1)) % 8 = ((p - 1) % 8 * ((p + 1) % 8)) % 8 := by
        rw [Nat.mul_mod]
      rw [h1, ha, hb]
    exact Nat.dvd_of_mod_eq_zero hmod
  · omega   -- p % 8 = 4 contradicts p odd
  · -- p % 8 = 5: (p-1)(p+1) % 8 = 4*6 % 8 = 0
    have hmod : (p - 1) * (p + 1) % 8 = 0 := by
      have ha : (p - 1) % 8 = 4 := by omega
      have hb : (p + 1) % 8 = 6 := by omega
      have h1 : ((p - 1) * (p + 1)) % 8 = ((p - 1) % 8 * ((p + 1) % 8)) % 8 := by
        rw [Nat.mul_mod]
      rw [h1, ha, hb]
    exact Nat.dvd_of_mod_eq_zero hmod
  · omega   -- p % 8 = 6 contradicts p odd
  · -- p % 8 = 7: (p-1)(p+1) % 8 = 6*0 % 8 = 0
    have hmod : (p - 1) * (p + 1) % 8 = 0 := by
      have hb : (p + 1) % 8 = 0 := by omega
      have h1 : ((p - 1) * (p + 1)) % 8 = ((p - 1) % 8 * ((p + 1) % 8)) % 8 := by
        rw [Nat.mul_mod]
      rw [h1, hb, Nat.mul_zero, Nat.zero_mod]
    exact Nat.dvd_of_mod_eq_zero hmod


-- 3 divides (p-1)(p+1) when p is not divisible by 3
/-- 当 2 ≤ p 且 3 ∤ p 时 3 ∣ p² - 1 -/
theorem three_dvd_sq_sub_one (p : Nat) (hp_ge : 2 ≤ p) (hp3 : p % 3 ≠ 0) :
    3 ∣ (p - 1) * (p + 1) := by
  -- Case analysis on p mod 3: possible residues are 1, 2 (not 0)
  have : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases this with (h | h)
  · -- p % 3 = 1: (p-1)(p+1) % 3 = 0*2 % 3 = 0
    have hmod : (p - 1) * (p + 1) % 3 = 0 := by
      have ha : (p - 1) % 3 = 0 := by omega
      have h1 : ((p - 1) * (p + 1)) % 3 = ((p - 1) % 3 * ((p + 1) % 3)) % 3 := by
        rw [Nat.mul_mod]
      rw [h1, ha, Nat.zero_mul, Nat.zero_mod]
    exact Nat.dvd_of_mod_eq_zero hmod
  · -- p % 3 = 2: (p-1)(p+1) % 3 = 1*0 % 3 = 0
    have hmod : (p - 1) * (p + 1) % 3 = 0 := by
      have hb : (p + 1) % 3 = 0 := by omega
      have h1 : ((p - 1) * (p + 1)) % 3 = ((p - 1) % 3 * ((p + 1) % 3)) % 3 := by
        rw [Nat.mul_mod]
      rw [h1, hb, Nat.mul_zero, Nat.zero_mod]
    exact Nat.dvd_of_mod_eq_zero hmod


/-!
  === GENERALIZATION: Odd numbers coprime to 6 ===

  The main theorem 24 | p² - 1 actually holds for ALL odd numbers
  not divisible by 3, not just primes. This generalization reveals
  that primality is not the essential condition — only oddness and
  non-divisibility by 3 matter.
-/

-- Generalized: for any odd n not divisible by 3, 24 | n² - 1
/-- 奇数且不被 3 整除时 24 ∣ n⁴ - 1 -/
theorem odd_not_three_sq_sub_one_dvd (n : Nat) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    24 ∣ n ^ 2 - 1 := by
  have hn2 : n ^ 2 = n * n := by rw [Nat.pow_succ, Nat.pow_one]
  rw [hn2]
  -- Step 1: n % 3 ∈ {1, 2} → n² ≡ 1 (mod 3)
  have hmod3 : (n * n) % 3 = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (h | h)
    · have h1 : (n * n) % 3 = (n % 3 * (n % 3)) % 3 := by rw [Nat.mul_mod]
      rw [h1, h]
    · have h1 : (n * n) % 3 = (n % 3 * (n % 3)) % 3 := by rw [Nat.mul_mod]
      rw [h1, h]
  -- Step 2: n odd → n % 8 ∈ {1,3,5,7} → n² ≡ 1 (mod 8)
  have hmod8 : (n * n) % 8 = 1 := by
    have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
    rcases this with (h | h | h | h)
    · rw [Nat.mul_mod, h]
    · rw [Nat.mul_mod, h]
    · rw [Nat.mul_mod, h]
    · rw [Nat.mul_mod, h]
  -- Step 3: CRT: mod 3 × mod 8 → mod 24
  have hmod24 : (n * n) % 24 = 1 := by
    have : (n * n) % 24 < 24 := Nat.mod_lt (n * n) (by decide)
    have : (n * n) % 24 % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd (n * n) (by decide : 3 ∣ 24)]
      exact hmod3
    have : (n * n) % 24 % 8 = 1 := by
      rw [Nat.mod_mod_of_dvd (n * n) (by decide : 8 ∣ 24)]
      exact hmod8
    omega
  have : (n * n - 1) % 24 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero this


/-!
  === HIGHER POWER: 48 | n⁴ - 1 ===

  For odd n coprime to 6, not only 24 | n² - 1, but 48 | n⁴ - 1.

  Proof strategy:
  - n⁴ - 1 = (n² - 1)(n² + 1)
  - We know 24 | n² - 1 (from above)
  - n odd → n² odd → n² + 1 even → 2 | n² + 1
  - Therefore 24 × 2 = 48 | (n² - 1)(n² + 1)

  This shows that higher powers gain additional factors of 2.
-/


/-!
  === CONSECUTIVE PRODUCT: 24 | n³ - n ===

  For any odd n not divisible by 3, 24 | n³ - n.
  This is because n³ - n = n(n-1)(n+1), the product of
  three consecutive integers centered at n.

  Proof strategy:
  - n³ - n = n(n² - 1) = n · (n-1)(n+1)
  - 24 | (n-1)(n+1) from the main theorem
  - Therefore 24 | n · (n-1)(n+1)
-/

-- Helper: a² - 1 = (a-1)(a+1) for a ≥ 1
-- Proof: expand (a-1)(a+1) = a² - a + a - 1 = a² - 1
private theorem sq_sub_one_eq_mul_pm1_aux {a : Nat} (ha : 1 ≤ a) :
    a * a - 1 = (a - 1) * (a + 1) := by
  rw [Nat.mul_add, Nat.mul_one,
      Nat.mul_comm (a - 1) a,
      Nat.mul_sub_left_distrib, Nat.mul_one]
  -- Goal: a * a - 1 = a * a - a + (a - 1)
  have h1 : a * a - a + (a - 1) = a * a - a + a - 1 := by omega
  rw [h1]
  have h2 : a * a - a + a = a * a := by
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left a (by omega))
  rw [h2]

-- For any odd n not divisible by 3, 24 | n³ - n
-- Proof: n³ - n = n(n² - 1), and 24 | (n² - 1)
/-- 奇数且不被 3 整除时 48 ∣ n³ - n -/
theorem odd_not_three_cubed_sub_self_dvd (n : Nat) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    24 ∣ n ^ 3 - n := by
  have h24 : 24 ∣ n ^ 2 - 1 := odd_not_three_sq_sub_one_dvd n hodd h3
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h24 ⊢
  -- n*n*n - n = n*(n*n - 1) by algebraic identity
  rw [Nat.mul_assoc]
  rw [show n * (n * n) - n = n * (n * n) - n * 1 from by rw [Nat.mul_one]]
  rw [← Nat.mul_sub_left_distrib]
  exact Nat.dvd_mul_left_of_dvd h24 n


-- For any odd n not divisible by 3, 48 | n⁴ - 1
-- Proof: n⁴ - 1 = (n² - 1)(n² + 1), 24 | (n² - 1) and 2 | (n² + 1)
/-- 奇数且不被 3 整除时 48 ∣ n⁴ - 1 -/
theorem odd_not_three_fourth_sub_one_dvd (n : Nat) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    48 ∣ n ^ 4 - 1 := by
  have h24 : 24 ∣ n ^ 2 - 1 := odd_not_three_sq_sub_one_dvd n hodd h3
  have h2_np1 : 2 ∣ n ^ 2 + 1 := by
    have : n ^ 2 % 2 = 1 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      rw [Nat.mul_mod, hodd, Nat.one_mul, Nat.one_mod]
    omega
  -- Unfold powers to n*n form
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h24 h2_np1 ⊢
  by_cases h0 : n = 0
  · simp [h0]
  · have ha : 1 ≤ n * n := by
      have : 1 ≤ n := by omega
      calc 1 ≤ n := by omega
        _ ≤ n * n := Nat.le_mul_of_pos_left _ (by omega)
    have h_assoc : n * n * n * n = (n * n) * (n * n) := by ring_nf
    rw [h_assoc]
    rw [sq_sub_one_eq_mul_pm1_aux ha]
    have : 48 = 24 * 2 := by decide
    rw [this]
    exact Nat.mul_dvd_mul h24 h2_np1
/-!
  === STRUCTURAL: lcm(p-1, p+1) = (p-1)(p+1)/2 ===

  For odd p ≥ 3, since gcd(p-1, p+1) = 2, we have:
    lcm(p-1, p+1) = (p-1)(p+1) / gcd(p-1, p+1) = (p-1)(p+1) / 2

  This connects the gcd result to the lcm, completing the
  structural picture of the relationship between p-1 and p+1.
-/

-- For odd p ≥ 3, lcm(p-1, p+1) = (p-1)(p+1)/2
/-- lcm(p-1, p+1) = (p-1)(p+1)/2 -/
theorem lcm_pm1_eq_half_mul (p : Nat) (hge : 3 ≤ p) (hodd : p % 2 = 1) :
    (p - 1).lcm (p + 1) = (p - 1) * (p + 1) / 2 := by
  -- lcm(a, b) * gcd(a, b) = a * b
  have hlcm : (p - 1).lcm (p + 1) * (p - 1).gcd (p + 1) =
              (p - 1) * (p + 1) :=
    Nat.lcm_mul_gcd (p - 1) (p + 1)
  -- gcd(p-1, p+1) = 2
  have hgcd : (p - 1).gcd (p + 1) = 2 := gcd_pm1_eq_two p hge hodd
  -- lcm * 2 = (p-1)(p+1)
  have hlcm2 : (p - 1).lcm (p + 1) * 2 = (p - 1) * (p + 1) := by
    have := hlcm
    simp only [hgcd] at this
    exact this
  -- Therefore lcm = (p-1)(p+1) / 2
  have h2_pos : 0 < 2 := by decide
  have h2_dvd : 2 ∣ (p - 1) * (p + 1) := by omega
  have : (p - 1) * (p + 1) / 2 = (p - 1).lcm (p + 1) := by
    rw [Nat.div_eq_iff_eq_mul_right h2_pos h2_dvd]
    omega
  exact this.symm


/-!
  === QUOTIENT BOUNDS ===

  For primes p ≥ 5, the quotient (p² - 1)/24 is always a positive integer.
  Moreover, for p ≥ 7, the quotient is at least 2.
-/

-- For primes p ≥ 5, (p² - 1)/24 ≥ 1
/-- (p²-1)/24 ≥ 1（素数 p ≥ 5）-/
theorem sq_sub_one_div_24_ge_one (p : Nat) (hp : Nat.Prime p) (hge : 5 ≤ p) :
    1 ≤ (p ^ 2 - 1) / 24 := by
  have h24 : 24 ∣ p ^ 2 - 1 := prime_ge_five_sq_sub_one_dvd p hp hge
  have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  rw [Nat.le_div_iff_mul_le (by decide), hp2]
  have : p ≥ 5 := hge
  have : p * p ≥ 25 := Nat.mul_le_mul this this
  omega


-- For primes p ≥ 7, (p² - 1)/24 ≥ 2
/-- (p²-1)/24 ≥ 2（素数 p ≥ 7）-/
theorem sq_sub_one_div_24_ge_two (p : Nat) (hp : Nat.Prime p) (hge : 7 ≤ p) :
    2 ≤ (p ^ 2 - 1) / 24 := by
  have h24 : 24 ∣ p ^ 2 - 1 := prime_ge_five_sq_sub_one_dvd p hp (by omega)
  have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  rw [Nat.le_div_iff_mul_le (by decide), hp2]
  have : p ≥ 7 := hge
  have : p * p ≥ 49 := Nat.mul_le_mul this this
  omega


/-!
  === PRIME MODULO 12 ===
  For primes p ≥ 5, p² ≡ 1 (mod 12).
-/

-- For primes p ≥ 5, p² ≡ 1 (mod 12)
/-- 素数 p ≥ 5 时 p² 模 12 余 1 -/
theorem prime_sq_mod_twelve (p : Nat) (hp : Nat.Prime p) (hge : 5 ≤ p) :
    p ^ 2 % 12 = 1 := by
  have h6 := prime_ge_five_mod_six p hp hge
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [Nat.mul_mod p p 12]
  rcases h6 with (h6 | h6)
  · have : p % 12 = 1 ∨ p % 12 = 7 := by omega
    rcases this with (h | h) <;> rw [h]
  · have : p % 12 = 5 ∨ p % 12 = 11 := by omega
    rcases this with (h | h) <;> rw [h]


/-!
  === SUM OF SQUARES: p² + q² ≡ 2 (mod 24) ===
  For any two primes p, q ≥ 5, p² + q² ≡ 2 (mod 24).
-/

-- Helper: from p % 6, enumerate p % 24
private theorem mod6_to_mod24 (p : Nat) (h6 : p % 6 = 1 ∨ p % 6 = 5) :
    p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
    p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
  rcases h6 with (h6 | h6) <;> omega

-- For each residue mod 24: x² % 24 = 1
private theorem sq_mod24_of_residue (x : Nat)
    (hx : x = 1 ∨ x = 5 ∨ x = 7 ∨ x = 11 ∨
           x = 13 ∨ x = 17 ∨ x = 19 ∨ x = 23) :
    (x * x) % 24 = 1 := by
  rcases hx with (h | h | h | h | h | h | h | h) <;> rw [h]

-- For any two primes p, q ≥ 5, (p² + q²) % 24 = 2
/-- 两素数平方和模 24 -/
theorem prime_sq_sum_mod_24 (p q : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_ge : 5 ≤ p) (hq_ge : 5 ≤ q) :
    (p ^ 2 + q ^ 2) % 24 = 2 := by
  have h6p := prime_ge_five_mod_six p hp hp_ge
  have h6q := prime_ge_five_mod_six q hq hq_ge
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [Nat.add_mod, Nat.mul_mod p p 24, Nat.mul_mod q q 24]
  rw [sq_mod24_of_residue (p % 24) (mod6_to_mod24 p h6p)]
  rw [sq_mod24_of_residue (q % 24) (mod6_to_mod24 q h6q)]


/-!
  === SUM OF SQUARES: p² + q² ≡ 2 (mod 8) ===
  For any two primes p, q ≥ 5, p² + q² ≡ 2 (mod 8).
-/

-- For each odd residue mod 8: x² % 8 = 1
private theorem sq_mod8_of_odd (x : Nat)
    (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) :
    (x * x) % 8 = 1 := by
  rcases hx with (h | h | h | h) <;> rw [h]

-- For any two primes p, q ≥ 5, (p² + q²) % 8 = 2
/-- 两素数平方和模 8 -/
theorem prime_sq_sum_mod_8 (p q : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp_ge : 5 ≤ p) (hq_ge : 5 ≤ q) :
    (p ^ 2 + q ^ 2) % 8 = 2 := by
  have hp_odd : p % 2 = 1 := by
    have := prime_not_dvd_of_range hp hp_ge (show 1 < 2 from by omega) (by omega)
    omega
  have hq_odd : q % 2 = 1 := by
    have := prime_not_dvd_of_range hq hq_ge (show 1 < 2 from by omega) (by omega)
    omega
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [Nat.add_mod, Nat.mul_mod p p 8, Nat.mul_mod q q 8]
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  have hq8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  rw [sq_mod8_of_odd (p % 8) hp8]
  rw [sq_mod8_of_odd (q % 8) hq8]


/-!
  === PRODUCT OF CONSECUTIVE FACTORS ===
  For primes p ≥ 7, (p-1)(p+1)/24 ≥ 2.
-/


