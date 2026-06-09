-- Von Mangoldt 函数与 Mertens 第一定理
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
open ArithmeticFunction (vonMangoldt vonMangoldt_apply_one vonMangoldt_nonneg vonMangoldt_apply_prime vonMangoldt_apply_pow vonMangoldt_ne_zero_iff vonMangoldt_pos_iff vonMangoldt_eq_zero_iff vonMangoldt_sum vonMangoldt_mul_zeta zeta_mul_vonMangoldt log_mul_moebius_eq_vonMangoldt moebius_mul_log_eq_vonMangoldt sum_moebius_mul_log_eq)
open Set Filter Topology Real; open scoped BigOperators
local notation "ψ" => Chebyshev.psi; local notation "θ" => Chebyshev.theta

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
theorem sum_vonMangoldt_eq_psi (n : ℕ) (hn : 0 < n) : ∑ k ∈ Finset.Icc 1 n, vonMangoldt k = ψ (n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc]; simp [Nat.floor_natCast]; omega

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
    _ ≤ 2 * (Real.sqrt p - 1) := by gcongr; _ < 2 * Real.sqrt p := by nlinarith

lemma sqrt_div_sq_eq_rpow (p : ℕ) (hp : 0 < p) : Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) = (p : ℝ) ^ (-3/2 : ℝ) := by
  have hp_pos : (p : ℝ) > 0 := by exact_mod_cast hp; have h_sub : (1/2 : ℝ) - (2 : ℝ) = (-3/2 : ℝ) := by ring
  calc Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) = ((p : ℝ) ^ (1/2 : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) := by rw [Real.sqrt_eq_rpow]
    _ = (p : ℝ) ^ ((1/2 : ℝ) - (2 : ℝ)) := by rw [← Real.rpow_sub hp_pos]; _ = (p : ℝ) ^ (-3/2 : ℝ) := by rw [h_sub]

lemma log_div_sq_bound_le (p : ℕ) (hp : 2 ≤ p) : Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) ≤ 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p from by omega)
  have h_log : Real.log (p : ℝ) < 2 * Real.sqrt (p : ℝ) := log_lt_two_sqrt hp'
  have h_sq_pos : (p : ℝ) ^ (2 : ℝ) > 0 := by positivity
  have h1 : Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) < (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) :=
    (div_lt_div_right h_sq_pos).mpr h_log
  have h2 : (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) ^ (2 : ℝ)) = 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := by
    calc _ = 2 * (Real.sqrt (p : ℝ) / ((p : ℝ) ^ (2 : ℝ))) := by ring
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
      have hk_eq : k = (k - 2) + 2 := by omega; rw [hk_eq, pow_add, div_div]; field_simp [hp_pos.ne'']; ring
    _ ≤ (1 / ((p : ℝ) ^ 2)) * (((1 : ℝ) / 2) ^ (k - 2)) := by
      gcongr; refine pow_le_pow_right (by positivity) ?_
      refine (one_div_le_one_div (by positivity) (by norm_num)).mpr ?_; exact_mod_cast hp
    _ = ((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2)) := by ring

lemma geom_tail_Icc_bound (p M : ℕ) (hp : 2 ≤ p) (hM : 2 ≤ M) : 
    ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / ((p : ℝ) ^ k) ≤ 2 / ((p : ℝ) ^ 2) := by
  have h_shift : ∑ k ∈ Finset.Icc 2 M, ((1 : ℝ) / 2) ^ (k - 2) = ∑ j ∈ Finset.range (M - 1), ((1 : ℝ) / 2) ^ j := by
    apply (Finset.sum_bij (λ k _ => k - 2) ?_ ?_ ?_ ?_ ?_).symm
    · intro k hk; apply Finset.mem_range.mpr; have hk2 := (Finset.mem_Icc.mp hk).1; have hkM := (Finset.mem_Icc.mp hk).2; omega
    · intro k hk; simp; · intro k1 hk1 k2 hk2 h; omega
    · intro j hj; rw [Finset.mem_range] at hj; have : j + 2 ∈ Finset.Icc 2 M := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      refine ⟨j + 2, this, ?_⟩; omega
    · rfl
  have h_sum : ∑ j ∈ Finset.range (M - 1), ((1 : ℝ) / 2) ^ j ≤ 2 := by
    have h_geom : ∑ j ∈ Finset.range (M - 1), ((1 : ℝ) / 2) ^ j = 2 * (1 - ((1 : ℝ) / 2) ^ (M - 1)) := by
      have h := geom_sum_eq (by norm_num : (1/2 : ℝ) ≠ 1) (M - 1); rw [h]; ring
    rw [h_geom]; have h_nonneg : 0 ≤ ((1 : ℝ) / 2) ^ (M - 1) := by positivity; nlinarith
  calc
    ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / ((p : ℝ) ^ k) ≤ ∑ k ∈ Finset.Icc 2 M, (((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2))) :=
      Finset.sum_le_sum (λ k hk => ?_)
    _ = (1 / ((p : ℝ) ^ 2)) * ∑ k ∈ Finset.Icc 2 M, ((1 : ℝ) / 2) ^ (k - 2) := by simp [Finset.mul_sum]
    _ = (1 / ((p : ℝ) ^ 2)) * ∑ j ∈ Finset.range (M - 1), ((1 : ℝ) / 2) ^ j := by rw [h_shift]
    _ ≤ (1 / ((p : ℝ) ^ 2)) * 2 := by gcongr
    _ = 2 / ((p : ℝ) ^ 2) := by ring
  · have hk := Finset.mem_Icc.mp hk; have hk2 : 2 ≤ k := hk.1
    calc (1 : ℝ) / ((p : ℝ) ^ k) = (1 / ((p : ℝ) ^ 2)) * ((1 / (p : ℝ)) ^ (k - 2)) := by
      have hk_eq : k = (k - 2) + 2 := by omega; rw [hk_eq, pow_add, div_div]; field_simp [show (p : ℝ) ≠ 0 from by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne']; ring
    _ ≤ (1 / ((p : ℝ) ^ 2)) * (((1 : ℝ) / 2) ^ (k - 2)) := by
      gcongr; refine pow_le_pow_right (by positivity) ?_
      refine (one_div_le_one_div (by positivity) (by norm_num)).mpr ?_; exact_mod_cast hp
    _ = ((1 : ℝ) / 2) ^ (k - 2) * (1 / ((p : ℝ) ^ 2)) := by ring

/-! === 第六部分: primePower_contribution_bounded (已证明) === -/
theorem primePower_contribution_bounded : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Icc 2 ⌊x⌋₊ with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ)| ≤ C := by
  let f (p : ℕ) : ℝ := if h : Nat.Prime p then 2 * (Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ))) else 0
  let g (p : ℕ) : ℝ := if h : Nat.Prime p then 4 * ((p : ℝ) ^ (-3/2 : ℝ)) else 0
  have h_f_nonneg : ∀ p, 0 ≤ f p := by intro p; dsimp [f]; split; intro hprime; positivity; rfl
  have h_g_nonneg : ∀ p, 0 ≤ g p := by intro p; dsimp [g]; split; intro hprime; positivity; rfl
  have h_g_summable : Summable g := by
    have h_summable_nat : Summable (fun n : ℕ => (n : ℝ) ^ (-3/2 : ℝ)) := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1))
    have h_indicator : Summable ((Nat.Primes : Set ℕ).indicator (fun n : ℕ => 4 * ((n : ℝ) ^ (-3/2 : ℝ)))) := Summable.indicator (h_summable_nat.const_smul 4) (Nat.Primes : Set ℕ)
    have h_eq : g = (Nat.Primes : Set ℕ).indicator (fun n : ℕ => 4 * ((n : ℝ) ^ (-3/2 : ℝ))) := by ext n; simp [g, Set.indicator, Set.mem_setOf_eq]
    rw [h_eq]; exact h_indicator
  have h_f_le_g : ∀ p, f p ≤ g p := by
    intro p; dsimp [f, g]; split <;> try { intro hprime; exfalso; exact hprime }; rfl
    · intro hprime; have hp2 : 2 ≤ p := Nat.Prime.two_le hprime
      have h_bound : Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ)) ≤ 2 * ((p : ℝ) ^ (-3/2 : ℝ)) := log_div_sq_bound_le p hp2
      calc 2 * (Real.log (p : ℝ) / ((p : ℝ) ^ (2 : ℝ))) ≤ 2 * (2 * ((p : ℝ) ^ (-3/2 : ℝ))) := by gcongr; _ = 4 * ((p : ℝ) ^ (-3/2 : ℝ)) := by ring
  have h_f_summable : Summable f := Summable.of_nonneg_of_le h_f_nonneg h_f_le_g h_g_summable
  set C := ∑' p, f p; refine ⟨C, λ x hx => ?_⟩; set N := ⌊x⌋₊
  have hN : 2 ≤ N := by have : 2 ≤ x := hx; have : (2 : ℕ) ≤ ⌊x⌋ := by exact_mod_cast (Nat.floor_mono this); omega
  have h_sum_nonneg : 0 ≤ ∑ n ∈ Finset.Icc 2 N with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) :=
    Finset.sum_nonneg (λ n hn => by have h_lambda_nonneg : 0 ≤ (vonMangoldt n : ℝ) := vonMangoldt_nonneg n; positivity)
  rw [abs_of_nonneg h_sum_nonneg]
  have h_total : ∑ n ∈ Finset.Icc 2 N with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), f p := by
    let primes : Finset ℕ := Finset.filter Nat.Prime (Finset.range (N + 1))
    have h_group : ∑ n ∈ Finset.Icc 2 N with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ p ∈ primes, ∑ n ∈ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N), (vonMangoldt n : ℝ) / (n : ℝ) := by
      have h_disjoint : ∀ p1 p2 ∈ primes, p1 ≠ p2 → Disjoint (Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p1) (Finset.Icc 2 N)) (Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p2) (Finset.Icc 2 N)) := by
        intro p1 hp1 p2 hp2 hne; apply Finset.disjoint_filter_filter; intro n hn h; have h1 : Nat.minFac n = p1 := h.2; have h2 : Nat.minFac n = p2 := h.2; exact hne (h1.trans h2.symm)
      have h_cover : (Finset.Icc 2 N).filter (¬Nat.Prime ·) = Finset.biUnion primes (λ p => Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N)) := by
        ext n; constructor
        · intro hn; have hn_ic := (Finset.mem_filter.mp hn).1; have hn_np : ¬Nat.Prime n := (Finset.mem_filter.mp hn).2
          have hmn2 : n ≠ 0 := by have : 2 ≤ n := (Finset.mem_Icc.mp hn_ic).1; omega
          have hprime_min : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hmn2
          have hp_mem : Nat.minFac n ∈ primes := by apply Finset.mem_filter.mpr; refine ⟨Finset.mem_range.mpr (by have hmin_le_n : Nat.minFac n ≤ n := Nat.minFac_le_of_dvd hmn2 (Nat.minFac_dvd n); omega), hprime_min⟩
          apply Finset.mem_biUnion.mpr; refine ⟨Nat.minFac n, hp_mem, Finset.mem_filter.mpr ⟨hn_ic, ⟨hn_np, ?_⟩⟩⟩; rfl
        · intro hn; rcases Finset.mem_biUnion.mp hn with ⟨p, hp, hn'⟩; apply Finset.mem_filter.mpr; exact ⟨(Finset.mem_filter.mp hn').1, (Finset.mem_filter.mp hn').2.1⟩
      rw [Finset.sum_filter, h_cover, Finset.sum_biUnion h_disjoint]
    have h_group_bound : ∀ p ∈ primes, ∑ n ∈ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N), (vonMangoldt n : ℝ) / (n : ℝ) ≤ f p := by
      intro p hp; have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2; have hp2 : 2 ≤ p := Nat.Prime.two_le hp_prime
      let K_p : Finset ℕ := Finset.filter (λ k : ℕ => p ^ k ∈ Finset.Icc 2 N) (Finset.Icc 2 N)
      have h_pow_sum : ∑ n ∈ Finset.image (λ k : ℕ => p ^ k) K_p, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ k ∈ K_p, Real.log (p : ℝ) / ((p : ℝ) ^ k) := by
        calc
          ∑ n ∈ Finset.image (λ k : ℕ => p ^ k) K_p, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ k ∈ K_p, (vonMangoldt (p ^ k) : ℝ) / ((p ^ k : ℕ) : ℝ) :=
            Finset.sum_image (λ x hx y hy h => (Nat.pow_right_inj (by have : 1 < p := Nat.Prime.one_lt hp_prime; exact this)).mp h)
          _ = ∑ k ∈ K_p, Real.log (p : ℝ) / ((p : ℝ) ^ k) := by
            refine Finset.sum_congr rfl (λ k hk => ?_); have hk_nonzero : k ≠ 0 := by
              have hk2 : 2 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1; omega
            simp [vonMangoldt_prime p hp_prime, vonMangoldt_pow' p k hk_nonzero]
      have h_img_sub : Finset.image (λ k : ℕ => p ^ k) K_p ⊆ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N) := by
        intro n hn; rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
        have h_pow_N : p ^ k ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).2).2
        have hp_pow_ge2 : 2 ≤ p ^ k := by calc 2 ≤ 2 ^ k := pow_pos (by omega) k; _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hp2
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_Icc.mpr ⟨hp_pow_ge2, h_pow_N⟩, ?_, ?_⟩
        · apply Nat.not_prime_pow hp2 hk2
        · have : p ^ k ≠ 0 := pow_pos (Nat.Prime.pos hp_prime) k; simp [Nat.minFac_pow hp_prime k]
      have h_comp_zero : ∑ n ∈ (Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N) \ Finset.image (λ k : ℕ => p ^ k) K_p), (vonMangoldt n : ℝ) / (n : ℝ) = 0 := by
        refine Finset.sum_eq_zero (λ n hn => ?_)
        have hn_mem : n ∈ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N) := (Finset.mem_sdiff.mp hn).1
        have hn_not_img : n ∉ Finset.image (λ k : ℕ => p ^ k) K_p := (Finset.mem_sdiff.mp hn).2
        have h_not_ppow : ¬IsPrimePow n := by
          intro h_ppow; have h_min : Nat.minFac n = p := (Finset.mem_filter.mp hn_mem).2.2
          have h_is_pow : ∃ e : ℕ, n = p ^ e := Nat.eq_pow_of_minFac_eq_prime h_ppow h_min
          rcases h_is_pow with ⟨e, h_eq⟩
          have h_in_K : e ∈ K_p := by
            apply Finset.mem_filter.mpr; refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
            · have : 2 ≤ e := by
                have h_n_np : ¬Nat.Prime n := (Finset.mem_filter.mp hn_mem).2.1
                by_contra! h; have h_e1 : e = 1 := by omega; subst h_e1; simp at h_eq
                exact h_n_np (by rw [h_eq]; exact hp_prime)
              omega
            · have h_n_le_N : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem).1).2; rw [h_eq] at h_n_le_N; exact h_n_le_N
            · rw [h_eq]; exact (Finset.mem_filter.mp hn_mem).1
          apply hn_not_img; apply Finset.mem_image.mpr; exact ⟨e, h_in_K, h_eq⟩
        have h_vonM_zero : vonMangoldt n = 0 := (vonMangoldt_zero_iff n).mpr h_not_ppow; simp [h_vonM_zero]
      calc
        ∑ n ∈ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N), (vonMangoldt n : ℝ) / (n : ℝ)
            = ∑ n ∈ Finset.image (λ k : ℕ => p ^ k) K_p, (vonMangoldt n : ℝ) / (n : ℝ) + ∑ n ∈ (Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N) \ Finset.image (λ k : ℕ => p ^ k) K_p), (vonMangoldt n : ℝ) / (n : ℝ) := by rw [Finset.sum_sdiff h_img_sub]
        _ = ∑ n ∈ Finset.image (λ k : ℕ => p ^ k) K_p, (vonMangoldt n : ℝ) / (n : ℝ) + 0 := by rw [h_comp_zero]
        _ = ∑ n ∈ Finset.image (λ k : ℕ => p ^ k) K_p, (vonMangoldt n : ℝ) / (n : ℝ) := by simp
        _ = ∑ k ∈ K_p, Real.log (p : ℝ) / ((p : ℝ) ^ k) := h_pow_sum
        _ ≤ ∑ k ∈ Finset.Icc 2 N, Real.log (p : ℝ) / ((p : ℝ) ^ k) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = Real.log (p : ℝ) * ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((p : ℝ) ^ k) := by simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _ ≤ Real.log (p : ℝ) * (2 / ((p : ℝ) ^ 2)) := by gcongr; apply geom_tail_Icc_bound p hp2 N hN
        _ = f p := by dsimp [f]; simp [hp_prime]; ring
    calc
      ∑ n ∈ Finset.Icc 2 N with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ p ∈ primes, ∑ n ∈ Finset.filter (λ n : ℕ => ¬Nat.Prime n ∧ Nat.minFac n = p) (Finset.Icc 2 N), (vonMangoldt n : ℝ) / (n : ℝ) := h_group
      _ ≤ ∑ p ∈ primes, f p := Finset.sum_le_sum (λ p hp => h_group_bound p hp)
  calc
    ∑ n ∈ Finset.Icc 2 N with ¬Nat.Prime n, (vonMangoldt n : ℝ) / (n : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), f p := h_total
    _ = ∑ p ∈ Finset.range (N + 1), f p := by simp [Finset.sum_filter]
    _ ≤ ∑' p, f p := range_sum_le_tsum_of_nonneg f h_f_nonneg h_f_summable (N + 1)
    _ = C := rfl


/-! === 第七部分: Mertens 第一定理 (4定理, 待完善) === -/

/-- Abel 求和恒等式 -/
theorem mertens_abel_identity (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
  have hc0 : vonMangoldt 0 = 0 := rfl
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ (λ u : ℝ => u⁻¹) t := by
    intro t ht; have ht_pos : t ≠ 0 := by linarith [ht.1, ht.2]; exact differentiableAt_inv ht_pos
  have hf_int : IntegrableOn (deriv (λ u : ℝ => u⁻¹)) (Set.Icc (1 : ℝ) x) := by
    have h_cont : ContinuousOn (λ t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) x) := by
      refine (Continuous.neg ((continuous_id.pow 2).inv₀ (λ t ht => ?_))).continuousOn
      have : 1 ≤ t := ht.1; nlinarith
    have h_deriv : deriv (λ u : ℝ => u⁻¹) = λ t : ℝ => -(t ^ 2)⁻¹ := by ext t; simp [deriv_inv]
    rw [h_deriv]; exact h_cont.integrableOn_Icc
  have h_formula := sum_mul_eq_sub_integral_mul₀ (c := vonMangoldt) hc0 x hf_diff hf_int
  have h_left : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((n : ℝ)⁻¹) * (vonMangoldt n : ℝ) := by
    refine Finset.sum_congr rfl (λ n hn => ?_)
    by_cases hn0 : n = 0; subst hn0; simp; field_simp [show (n : ℝ) ≠ 0 from by exact_mod_cast hn0]; ring
  have h_right1 : ((x : ℝ)⁻¹) * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n) = ψ x / x := by
    rw [Chebyshev.psi_eq_sum_Icc x]; field_simp [show x ≠ 0 from by linarith]; ring
  have h_right2 : ∫ t in Set.Ioc (1 : ℝ) x, (deriv (λ u : ℝ => u⁻¹) t) * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt n) = -∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
    have h_deriv : deriv (λ u : ℝ => u⁻¹) = λ t : ℝ => -(t ^ 2)⁻¹ := by ext t; simp [deriv_inv]
    rw [h_deriv, Chebyshev.psi_eq_sum_Icc]
    calc
      ∫ t : ℝ in Set.Ioc (1 : ℝ) x, (-(t ^ 2)⁻¹) * (ψ t) = ∫ t : ℝ in Set.Ioc (1 : ℝ) x, -(ψ t / (t * t)) := by
/-! === 第七部分: Mertens 第一定理 (4定理) === -/

/-- Abel 求和恒等式 (已证明) -/
theorem mertens_abel_identity (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
  have hc0 : vonMangoldt 0 = 0 := rfl
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ (λ u : ℝ => u⁻¹) t := by
    intro t ht; have ht_pos : t ≠ 0 := by linarith [ht.1, ht.2]; exact differentiableAt_inv ht_pos
  have hf_int : IntegrableOn (deriv (λ u : ℝ => u⁻¹)) (Set.Icc (1 : ℝ) x) := by
    have h_cont : ContinuousOn (λ t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) x) := by
      refine (Continuous.neg ((continuous_id.pow 2).inv₀ (λ t ht => ?_))).continuousOn
      have : 1 ≤ t := ht.1; nlinarith
    have h_deriv : deriv (λ u : ℝ => u⁻¹) = λ t : ℝ => -(t ^ 2)⁻¹ := by ext t; simp [deriv_inv]
    rw [h_deriv]; exact h_cont.integrableOn_Icc
  have h_formula := sum_mul_eq_sub_integral_mul₀ (c := vonMangoldt) hc0 x hf_diff hf_int
  have h_left : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((n : ℝ)⁻¹) * (vonMangoldt n : ℝ) := by
    refine Finset.sum_congr rfl (λ n hn => ?_)
    by_cases hn0 : n = 0; subst hn0; simp; field_simp [show (n : ℝ) ≠ 0 from by exact_mod_cast hn0]; ring
  have h_right1 : ((x : ℝ)⁻¹) * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n) = ψ x / x := by
    rw [Chebyshev.psi_eq_sum_Icc x]; field_simp [show x ≠ 0 from by linarith]; ring
  have h_right2 : ∫ t in Set.Ioc (1 : ℝ) x, (deriv (λ u : ℝ => u⁻¹) t) * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt n) = -∫ t in Set.Ioc 1 x, ψ t / (t * t) := by
    have h_deriv : deriv (λ u : ℝ => u⁻¹) = λ t : ℝ => -(t ^ 2)⁻¹ := by ext t; simp [deriv_inv]
    rw [h_deriv, Chebyshev.psi_eq_sum_Icc]
    calc
      ∫ t : ℝ in Set.Ioc (1 : ℝ) x, (-(t ^ 2)⁻¹) * (ψ t) = ∫ t : ℝ in Set.Ioc (1 : ℝ) x, -(ψ t / (t * t)) := by
        refine setIntegral_congr_set (Set.Ioc (1 : ℝ) x) (λ t ht => ?_)
        have ht_pos : t ≠ 0 := by have : 1 < t := ht.1; nlinarith; field_simp [ht_pos]; ring
      _ = -(∫ t : ℝ in Set.Ioc (1 : ℝ) x, ψ t / (t * t)) := by simp [integral_neg]
      _ = -∫ t in Set.Ioc 1 x, ψ t / (t * t) := rfl
  calc
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((n : ℝ)⁻¹) * (vonMangoldt n : ℝ) := h_left
    _ = ((x : ℝ)⁻¹) * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n) - ∫ t in Set.Ioc (1 : ℝ) x, (deriv (λ u : ℝ => u⁻¹) t) * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt n) := h_formula
    _ = (ψ x / x) - (-∫ t in Set.Ioc 1 x, ψ t / (t * t)) := by rw [h_right1, h_right2]
    _ = ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) := by ring

/-- 关键引理: ∫₁ˣ ψ(t)/t² dt - log x = O(1)
    等价于 ∫₁^∞ (ψ(t)-t)/t² dt 收敛, 即素数定理.
    当前待定 -/
theorem psi_integral_sub_log_isBigO : (fun x : ℝ ↦ ∫ t in Set.Ioc 1 x, ψ t / (t * t) - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry

/-- Mertens 第一定理的初等证明需要 Stirling 公式和卷积恒等式,
    当前为待定状态. -/

/-- Mertens 第一定理 (初等证明: ∑ Λ(n)/n = ∑ log n/x + O(ψ(x)/x)) -/
theorem mertens_first_theorem : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  have h_psi_bound : (fun x : ℝ ↦ ψ x / x) =O[atTop] (fun _ : ℝ ↦ (1 : ℝ)) := by
    refine Asymptotics.isBigO_of_le_atTop (λ x hx => ?_)
    have hx_nonneg : 0 ≤ x := by linarith
    have hbd : |ψ x| ≤ (Real.log 4 + 4) * x := psi_bounded x hx_nonneg
    have hpos : 0 ≤ ψ x := Chebyshev.psi_nonneg x
    have hx_pos : x > 0 := by by_contra! h; have : x ≤ 0 := h; linarith
    calc
      |ψ x / x| = |ψ x| / |x| := by rw [abs_div]
      _ = |ψ x| / x := by simp [hx_pos.le]
      _ ≤ ((Real.log 4 + 4) * x) / x := (div_le_div_right (by exact_mod_cast (by positivity : 0 < x))).mpr (by
        rw [abs_of_nonneg hpos, abs_of_nonneg hx_pos.le]; exact hbd)
      _ = Real.log 4 + 4 := by field_simp [hx_pos.ne']
    _ = (Real.log 4 + 4) * (1 : ℝ) := by ring
  have h_mertens_abel : ∀ x ≥ 1, ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) = ψ x / x + ∫ t in Set.Ioc 1 x, ψ t / (t * t) :=
    mertens_abel_identity
  
  -- 由 mertens_abel_identity: ∑ Λ/n = ψ/x + ∫ ψ/t² dt
  -- 所以: ∑ Λ/n - log x = ψ/x + (∫ ψ/t² dt - log x)
  -- 需要: ∫ ψ/t² dt - log x = O(1), 这等价于素数定理.
  -- 目前为待定: 需要 ∫_1^∞ (ψ(t) - t)/t² dt 收敛
  sorry

/-- Mertens 第一定理 (有界差版本) -/
theorem mertens_first_theorem_bounded : ∃ C : ℝ, ∀ᶠ x in atTop, |∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / (n : ℝ) - Real.log x| ≤ C := by
  rcases mertens_first_theorem.exists_bounded with ⟨C, hC⟩
  refine ⟨C, ?_⟩; filter_upwards [hC] with x hx; simpa using hx
