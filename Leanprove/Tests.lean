-- 回归测试: 验证所有关键定理的类型签名
-- 确保重构和新增代码不会破坏已有定理的接口
import Leanprove.Basic
import Leanprove.Bertrand
import Leanprove.Chebyshev
import Leanprove.Dirichlet
import Leanprove.PrimeCounting
import Leanprove.PrimeReciprocals
import Leanprove.VonMangoldt

/-!
  === Tests: 类型签名回归测试 ===

  用 #check 验证每个公开定理的类型签名是否正确。
  若某个定理被重命名、删除或类型发生变化, 构建将在此处报错。
-/

-- Basic.lean
#check prime_ge_five_mod_six
#check prime_ge_five_sq_sub_one_dvd
#check dvd_consecutive_eq_one
#check gcd_consecutive
#check dvd_sq_sub_one
#check sub_one_sub_sub_one
#check prime_sq_diff_dvd_24
#check sq_sub_one_eq_mul_pm1
#check gcd_pm1_eq_two
#check eight_dvd_sq_sub_one
#check three_dvd_sq_sub_one
#check odd_not_three_sq_sub_one_dvd
#check odd_not_three_cubed_sub_self_dvd
#check odd_not_three_fourth_sub_one_dvd
#check lcm_pm1_eq_half_mul
#check sq_sub_one_div_24_ge_one
#check sq_sub_one_div_24_ge_two
#check prime_sq_mod_twelve
#check prime_sq_sum_mod_24
#check prime_sq_sum_mod_8

-- Bertrand.lean
#check prime_counting_gap
#check interval_contains_prime
#check infinite_prime_pairs
#check infinite_primes
#check prime_ratio_bounded
#check bertrand_interval

-- Chebyshev.lean
#check theta_le_psi_le_const_mul
#check psi_le_explicit
#check psi_zero_of_lt_two'
#check theta_zero_of_lt_two'
#check psi_eq_log_lcm
#check theta_eq_log_primorial'
#check pi_lower_bound
#check pi_upper_bound
#check theta_le_pi_mul_log'
#check psi_le_pi_mul_log'
#check psi_ten_le
#check theta_ten_le
#check psi_hundred_le
#check theta_hundred_le

-- Dirichlet.lean
#check exists_prime_mod_four_eq_one_gt
#check infinite_primes_mod_four_eq_one
#check prime_dvd_sq_add_one_mod_four
#check prime_factor_sq_add_one
#check exists_prime_mod_four_eq_one_gt_elementary
#check exists_prime_factor_mod_four_eq_three
#check exists_prime_mod_four_eq_three_gt
#check infinite_primes_mod_four_eq_three
#check exists_prime_factor_mod_six_eq_five
#check exists_prime_mod_six_eq_five_gt
#check infinite_primes_mod_six_eq_five

-- PrimeCounting.lean
#check pi_lower_bound_simple
#check pi_upper_bound_simple
#check pi_tendsto_top

-- PrimeReciprocals.lean
#check not_summable_prime_reciprocal

-- Tests for Mertens theorems
#check mertens_abel_identity
#check psi_integral_sub_log_isBigO
#check mertens_first_theorem
#check mertens_first_theorem_bounded
