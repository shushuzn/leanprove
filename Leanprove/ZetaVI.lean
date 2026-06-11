/-
Phase VI: Riemann Xi function and Hardy's theorem.
ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Polynomial
import Leanprove.ZetaIVE

open Complex Real
open scoped Topology BigOperators

noncomputable section

/-- completed Riemann zeta: Λ(s) = π^{-s/2}Γ(s/2)ζ(s) -/
def completedZeta (s : ℂ) : ℂ :=
  (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s

lemma completedZeta_one_sub (s : ℂ) : completedZeta (1 - s) = completedZeta s :=
  completedRiemannZeta_one_sub s

/-- Riemann ξ 函数: ξ(s) = s(s-1)Λ(s) -/
def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedZeta s

lemma riemannXi_eq_riemannXi_one_sub (s : ℂ) : riemannXi s = riemannXi (1 - s) := by
  dsimp [riemannXi]
  have hΛ : completedZeta (1 - s) = completedZeta s := completedZeta_one_sub s
  calc
    s * (s - 1) * completedZeta s = (1 - s) * (-s) * completedZeta s := by ring
    _ = (1 - s) * ((1 - s) - 1) * completedZeta (1 - s) := by
      simp [hΛ]
      ring
    _ = riemannXi (1 - s) := rfl

/-- ξ 函数与复共轭交换: ξ(s̅) = ξ(s)̅ -/
lemma riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  dsimp [riemannXi, completedZeta]
  simp [map_mul, map_add, map_sub, conj_pow, conj_neg, conj_ofReal, Gamma_conj, riemannZeta_conj]

/-- 在临界线上 ξ(1/2 + it) 是实值函数 -/
lemma riemannXi_real_on_critical_line (t : ℝ) : riemannXi (1/2 + I * t) ∈ ℝ := by
  have h_symm : riemannXi (1/2 + I * t) = riemannXi (1/2 - I * t) := by
    calc
      riemannXi (1/2 + I * t) = riemannXi (1 - (1/2 + I * t)) := riemannXi_eq_riemannXi_one_sub _
      _ = riemannXi (1/2 - I * t) := by ring
  have h_conj : riemannXi (1/2 - I * t) = conj (riemannXi (1/2 + I * t)) := by
    calc
      riemannXi (1/2 - I * t) = riemannXi (conj (1/2 + I * t)) := by simp
      _ = conj (riemannXi (1/2 + I * t)) := riemannXi_conj _
  rw [h_symm, h_conj]
  exact conj_eq_self.mp rfl

/-- ξ 是整函数（利用 Λ₀ 的整函数性）-/
lemma riemannXi_isEntire : Differentiable ℂ riemannXi := by
  have h_formula : ∀ s : ℂ, riemannXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := by
    intro s
    dsimp [riemannXi, completedZeta]
    have hΛ_eq : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
      completedRiemannZeta_eq s
    rw [hΛ_eq]
    ring
  refine (Differentiable.mul ?_ ?_).add (differentiable_const 1)
  · exact differentiable_id.mul (differentiable_id.sub differentiable_const)
  · exact differentiable_completedZeta₀

/-! #### 增长估计 -/

/-- ζ(s) 在 Re(s) = 2 上绝对收敛：|ζ(2 + it)| ≤ ζ(2) -/
lemma zeta_bound_at_two (t : ℝ) : ‖riemannZeta (2 + I * t)‖ ≤ riemannZeta (2 : ℂ) := by
  have hs : 1 < (2 + I * t).re := by
    simp
    norm_num
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hsum : Summable (fun n : ℕ => ‖1 / ((n : ℂ) ^ (2 + I * t))‖) := by
    have h_abs_eq : ∀ n : ℕ, n ≠ 0 → ‖1 / ((n : ℂ) ^ (2 + I * t))‖ = 1 / ((n : ℝ) ^ (2 : ℝ)) := by
      intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos (2 + I * t), norm_natCast,
        norm_ofReal]
    refine .of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (by
      refine (summable_nat_add_iff 1).mpr ?_
      have : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℝ))) := by
        simpa using Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < (2 : ℝ))
      convert this
      ext n
      simp)
    by_cases hn0 : n = 0
    · subst hn0; simp
    · rw [h_abs_eq n hn0]
      exact le_rfl
  calc
    ‖∑' n : ℕ, 1 / ((n : ℂ) ^ (2 + I * t))‖ ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) ^ (2 + I * t))‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ (2 : ℝ)) := by
      refine tsum_congr (fun n => ?_)
      by_cases hn0 : n = 0
      · subst hn0; simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        simp [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos (2 + I * t), norm_natCast,
          norm_ofReal]
    _ = riemannZeta (2 : ℂ) := by
      have h2 : 1 < (2 : ℂ).re := by norm_num
      rw [zeta_eq_tsum_one_div_nat_cpow h2]
      simp [div_eq_inv_mul]

/-- 通过函数方程：|ζ(-1 + it)| ≤ C_t * |ζ(2 + it)|，其中 C_t 多项式增长 -/
lemma zeta_bound_at_neg_one (t : ℝ) : ‖riemannZeta (-1 + I * t)‖ ≤
    ‖2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) * cos (π * (2 - I * t) / 2)‖ *
    ‖riemannZeta (2 + I * t)‖ := by
  have hs : ∀ n : ℕ, (2 - I * t) ≠ -n := by
    intro n h
    have : ((2 - I * t) + n).re = 0 := by simpa [h] using rfl
    simp at this
  have hs' : (2 - I * t) ≠ 1 := by
    intro h; have : (2 - I * t).im = 1.im := by simpa [h]
    simp at this
  have h_func : riemannZeta (-1 + I * t) =
      2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) * cos (π * (2 - I * t) / 2) *
      riemannZeta (2 + I * t) := by
    calc
      riemannZeta (-1 + I * t) = riemannZeta (1 - (2 - I * t)) := by ring
      _ = 2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) *
          cos (π * (2 - I * t) / 2) * riemannZeta (2 - I * t) := by
        rw [riemannZeta_one_sub hs hs']
      _ = 2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) *
          cos (π * (2 - I * t) / 2) * riemannZeta (2 + I * t) := by
        simp [riemannZeta_conj, conj_I, map_sub, add_comm]
  rw [h_func]
  calc
    ‖2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) * cos (π * (2 - I * t) / 2) *
      riemannZeta (2 + I * t)‖
        ≤ ‖2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) * cos (π * (2 - I * t) / 2)‖ *
          ‖riemannZeta (2 + I * t)‖ :=
      norm_mul_le _ _
    _ = ‖2 * ((2 * π : ℂ) ^ (-(2 - I * t))) * Gamma (2 - I * t) * cos (π * (2 - I * t) / 2)‖ *
      ‖riemannZeta (2 + I * t)‖ := rfl

/-- ξ(s) 在实轴上取实值 -/
lemma riemannXi_real_on_real (s : ℝ) : riemannXi (s : ℂ) ∈ ℝ := by
  have : (s : ℂ).conj = (s : ℂ) := by simp
  simpa [this] using (riemannXi_conj (s : ℂ)).symm ▸ (conj_eq_self.mp ?_)
  calc
    conj (riemannXi (s : ℂ)) = riemannXi (conj (s : ℂ)) := (riemannXi_conj (s : ℂ)).symm
    _ = riemannXi (s : ℂ) := by simp

/-- ξ(0) = 1（利用 Λ₀ 的正则化公式） -/
lemma riemannXi_zero : riemannXi 0 = 1 := by
  have h_formula : riemannXi 0 = (0 : ℂ) * ((0 : ℂ) - 1) * completedRiemannZeta₀ (0 : ℂ) + 1 := by
    simpa using (show ∀ s : ℂ, riemannXi s = s * (s - 1) * completedRiemannZeta₀ s + 1 from ?_) 0
  · simp [h_formula]
  · intro s
    dsimp [riemannXi, completedZeta]
    have hΛ_eq : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
      completedRiemannZeta_eq s
    rw [hΛ_eq]
    ring

/-- ξ(1) = 1（对称性） -/
lemma riemannXi_one : riemannXi 1 = 1 := by
  simpa [riemannXi_eq_riemannXi_one_sub, sub_self] using riemannXi_zero

/-! #### Lemma 1: |Γ(it)| 的下界（通过反射公式） -/

/-- sin(iθ) = i·sinh(θ) -/
lemma sin_mul_I (θ : ℝ) : Complex.sin (I * (θ : ℂ)) = I * Complex.sinh (θ : ℂ) := by
  rw [Complex.sin, Complex.sinh, mul_comm (I * (θ : ℂ))]
  simp [exp_mul_I, mul_comm, mul_left_comm, mul_assoc]

/-- |Γ(it)|² = π / (|t|·|sinh(πt)|)  — 来自反射公式和函数方程 -/
lemma gamma_it_sq_norm (t : ℝ) (ht : t ≠ 0) : ‖Gamma (I * (t : ℂ))‖ ^ 2 = π / |t| / |Real.sinh (π * t)| := by
  have h_reflect : Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ)) = π / sin (π * (I * (t : ℂ))) :=
    Complex.Gamma_mul_Gamma_one_sub (I * (t : ℂ))
  have h_add : Gamma (1 - I * (t : ℂ)) = (-I * (t : ℂ)) * Gamma (-I * (t : ℂ)) := by
    calc
      Gamma (1 - I * (t : ℂ)) = Gamma ((-I * (t : ℂ)) + 1) := by ring
      _ = (-I * (t : ℂ)) * Gamma (-I * (t : ℂ)) :=
        Complex.Gamma_add_one (-I * (t : ℂ)) (by
          intro hzero; apply ht; simpa [mul_eq_zero] using hzero)
  have h_norm_gamma_conj : ‖Gamma (-I * (t : ℂ))‖ = ‖Gamma (I * (t : ℂ))‖ := by
    calc
      ‖Gamma (-I * (t : ℂ))‖ = ‖conj (Gamma (I * (t : ℂ)))‖ := by
        simp [Complex.Gamma_conj (I * (t : ℂ))]
      _ = ‖Gamma (I * (t : ℂ))‖ := norm_conj _
  have h_sin_sinh : sin (π * (I * (t : ℂ))) = I * Complex.sinh (π * (t : ℂ)) := by
    calc
      sin (π * (I * (t : ℂ))) = sin (I * (π * (t : ℂ))) := by ring
      _ = I * Complex.sinh (π * (t : ℂ)) := sin_mul_I (π * t)
  have h_norm_sin : ‖sin (π * (I * (t : ℂ)))‖ = |Real.sinh (π * t)| := by
    rw [h_sin_sinh, norm_mul, norm_I, one_mul, Complex.norm_sinh_eq_abs_sinh (π * t)]
    simp
  have h_norm_reflect : ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ = π / |t| / |Real.sinh (π * t)| := by
    rw [h_reflect, h_add, mul_assoc, norm_mul, norm_mul, norm_div, norm_norm, norm_norm,
      norm_ofReal, norm_neg, norm_I, norm_norm, h_norm_gamma_conj, h_norm_sin]
    have ht_abs : |t| ≠ 0 := by simpa using ht
    field_simp [ht_abs]
    ring
  have h_prod_norm : ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ =
    ‖Gamma (I * (t : ℂ))‖ * |t| * ‖Gamma (I * (t : ℂ))‖ := by
    rw [h_add, mul_assoc, norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_norm, h_norm_gamma_conj]
    ring
  have h_eq : ‖Gamma (I * (t : ℂ))‖ ^ 2 * |t| = π / |t| / |Real.sinh (π * t)| * |t| := by
    calc
      ‖Gamma (I * (t : ℂ))‖ ^ 2 * |t| = (‖Gamma (I * (t : ℂ))‖ * |t| * ‖Gamma (I * (t : ℂ))‖) := by ring
      _ = ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ := by rw [h_prod_norm]
      _ = π / |t| / |Real.sinh (π * t)| := h_norm_reflect
      _ = π / |t| / |Real.sinh (π * t)| * |t| := by ring
  have hpos : 0 < |t| := abs_pos.mpr ht
  have h_nonneg : 0 ≤ ‖Gamma (I * (t : ℂ))‖ := norm_nonneg _
  nlinarith  rw [Complex.sin, Complex.sinh, sub_eq_add_neg, mul_comm, mul_comm (I * (θ : ℂ))]
  simp [exp_mul_I, mul_comm, add_comm, sub_eq_add_neg]

/-- |Γ(it)|² = π / (|t|·|sinh(πt)|)  — 来自反射公式和函数方程 -/
lemma gamma_it_sq_norm (t : ℝ) (ht : t ≠ 0) : ‖Gamma (I * (t : ℂ))‖ ^ 2 = π / |t| / |Real.sinh (π * t)| := by
  have h_reflect : Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ)) = π / sin (π * (I * (t : ℂ))) :=
    Complex.Gamma_mul_Gamma_one_sub (I * (t : ℂ))
  have h_add : Gamma (1 - I * (t : ℂ)) = (-I * (t : ℂ)) * Gamma (-I * (t : ℂ)) := by
    calc
      Gamma (1 - I * (t : ℂ)) = Gamma ((-I * (t : ℂ)) + 1) := by ring
      _ = (-I * (t : ℂ)) * Gamma (-I * (t : ℂ)) :=
        Complex.Gamma_add_one (-I * (t : ℂ)) (by
          intro hzero; apply ht; simpa [mul_eq_zero] using hzero)
  have h_conj_norm : ‖Gamma (-I * (t : ℂ))‖ = ‖Gamma (I * (t : ℂ))‖ := by
    calc
      ‖Gamma (-I * (t : ℂ))‖ = ‖conj (Gamma (I * (t : ℂ)))‖ := by
        simp [Complex.Gamma_conj (I * (t : ℂ))]
      _ = ‖Gamma (I * (t : ℂ))‖ := norm_conj _
  have h_sin_norm : ‖sin (π * (I * (t : ℂ)))‖ = |Real.sinh (π * t)| := by
    calc
      ‖sin (π * (I * (t : ℂ)))‖ = ‖I * Complex.sinh (π * (t : ℂ))‖ := by
        simp [sin_mul_I, mul_assoc, mul_comm π]
      _ = ‖Complex.sinh (π * (t : ℂ))‖ := by simp
      _ = |Real.sinh (π * t)| := by simp [Complex.sinh_ofReal]
  have h_norm_reflect : ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ = π / |t| / |Real.sinh (π * t)| := by
    rw [h_reflect, h_add, mul_assoc, norm_mul, norm_mul, norm_div, norm_norm, norm_norm,
      norm_ofReal, norm_neg, norm_I, norm_norm, h_conj_norm, h_sin_norm]
    have ht_abs : |t| ≠ 0 := by simpa using ht
    field_simp [ht_abs]
    ring
  have h_prod_norm : ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ =
    ‖Gamma (I * (t : ℂ))‖ * |t| * ‖Gamma (I * (t : ℂ))‖ := by
    rw [h_add, mul_assoc, norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_norm, h_conj_norm]
    ring
  have h_eq : ‖Gamma (I * (t : ℂ))‖ ^ 2 * |t| = π / |t| / |Real.sinh (π * t)| * |t| := by
    calc
      ‖Gamma (I * (t : ℂ))‖ ^ 2 * |t| = (‖Gamma (I * (t : ℂ))‖ * |t| * ‖Gamma (I * (t : ℂ))‖) := by ring
      _ = ‖Gamma (I * (t : ℂ)) * Gamma (1 - I * (t : ℂ))‖ := by rw [h_prod_norm]
      _ = π / |t| / |Real.sinh (π * t)| := h_norm_reflect
      _ = π / |t| / |Real.sinh (π * t)| * |t| := by ring
  have hpos : 0 < |t| := abs_pos.mpr ht
  have h_nonneg : 0 ≤ ‖Gamma (I * (t : ℂ))‖ := norm_nonneg _
  field_simp [hpos.ne.symm]
  nlinarith

/-! ### 零点计数函数 N(T) -/

/-- Riemann ξ 函数的零点集 -/
def riemannXiZeros : Set ℂ := {z | riemannXi z = 0}

/-- 高度为 T 的临界带区域：{z ∈ ℂ | 0 ≤ Re(z) ≤ 1, 0 ≤ Im(z) ≤ T} -/
def criticalStrip (T : ℝ) : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ T}

/-- 零点计数函数 N(T) = #{ρ ∈ criticalStrip T | ξ(ρ) = 0} -/
def xiZeroCount (T : ℝ) : ℕ := Nat.card (riemannXiZeros ∩ criticalStrip T)

/-! #### criticalStrip 的基本性质 -/

lemma criticalStrip_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    criticalStrip T₁ ⊆ criticalStrip T₂ := by
  intro z hz
  simp only [criticalStrip, Set.mem_setOf_eq] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.1, le_trans hz.2.2.2 h⟩

lemma criticalStrip_isClosed (T : ℝ) : IsClosed (criticalStrip T) := by
  have h1 : IsClosed {z : ℂ | 0 ≤ z.re} := isClosed_le continuous_const continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ 1} := isClosed_le continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ T} := isClosed_le continuous_im continuous_const
  simpa [criticalStrip] using h1.inter (h2.inter (h3.inter h4))

lemma criticalStrip_bounded (T : ℝ) : Metric.Bounded (criticalStrip T) := by
  apply Metric.Bounded.subset_ball (0 : ℂ) (max 1 (|T| + 1))
  intro z hz
  have h₁ : 0 ≤ z.re := hz.1
  have h₂ : z.re ≤ 1 := hz.2.1
  have h₃ : 0 ≤ z.im := hz.2.2.1
  have h₄ : z.im ≤ T := hz.2.2.2
  have h₅ : |z.re| ≤ 1 := by
    rw [abs_of_nonneg h₁] <;> linarith
  have h₆ : |z.im| ≤ |T| := by
    have h₇ : 0 ≤ z.im := h₃
    rw [abs_of_nonneg h₇]
    cases' le_total 0 T with hT hT <;> rw [abs_of_nonneg hT] <;> linarith
  have h₇ : ‖z‖ ≤ max 1 (|T| + 1) := by
    have h₈ : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    linarith
  exact Metric.mem_ball'.mpr h₇

lemma criticalStrip_isCompact (T : ℝ) : IsCompact (criticalStrip T) := by
  exact HeineBorel.isCompact_iff_isClosed_isBounded.mpr
    ⟨criticalStrip_isClosed T, criticalStrip_bounded T⟩

/-! #### riemannXiZeros 的基本性质 -/

lemma zero_notin_riemannXiZeros : (0 : ℂ) ∉ riemannXiZeros := by
  simpa [riemannXiZeros, riemannXi_zero] using show (1 : ℂ) ≠ 0 from by norm_num

lemma one_notin_riemannXiZeros : (1 : ℂ) ∉ riemannXiZeros := by
  simpa [riemannXiZeros, riemannXi_one] using show (1 : ℂ) ≠ 0 from by norm_num

lemma riemannXiZeros_symm_one_sub : ∀ z ∈ riemannXiZeros, 1 - z ∈ riemannXiZeros := by
  intro z hz
  have h1 : riemannXi z = 0 := hz
  have h2 : riemannXi (1 - z) = riemannXi z := riemannXi_eq_riemannXi_one_sub z
  simpa [riemannXiZeros, h2, h1] using rfl

lemma riemannXiZeros_symm_conj : ∀ z ∈ riemannXiZeros, conj z ∈ riemannXiZeros := by
  intro z hz
  have h1 : riemannXi z = 0 := hz
  have h2 : riemannXi (conj z) = conj (riemannXi z) := riemannXi_conj z
  simpa [riemannXiZeros, h2, h1] using by simp

/-! #### xiZeroCount (N(T)) 的基本性质 -/

lemma xiZeroCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    xiZeroCount T₁ ≤ xiZeroCount T₂ := by
  apply Nat.card_le_card (Set.inter_subset_inter_right _ (criticalStrip_mono h))

/-- 当 ξ(z) = 0 且 z ≠ 0,1 时，有 ζ(z) = 0。
    即 ξ 的非平凡零点即为 ζ 的非平凡零点。 -/
lemma riemannXi_zero_implies_zeta_zero {z : ℂ} (hz : z ∈ riemannXiZeros) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    riemannZeta z = 0 := by
  have h1 : riemannXi z = 0 := hz
  have h2 : riemannXi z = z * (z - 1) * completedZeta z := by rfl
  rw [h2] at h1
  have h3 : z * (z - 1) ≠ 0 := by
    simp [hz0, hz1, sub_ne_zero.mpr]
    <;> tauto
  have h4 : completedZeta z = 0 := (mul_eq_zero.mp h1).resolve_left h3
  have h5 : (π : ℂ) ^ (-z / 2) ≠ 0 := by
    exact pow_ne_zero _ _
  have h6 : Gamma (z / 2) ≠ 0 := by
    exact Complex.Gamma_ne_zero (z / 2)
  simpa [completedZeta, h5, h6] using mul_eq_zero.mp (mul_eq_zero.mp h4)

/-- `xiZeroCount` 即解析数论中的零点计数函数 N(T)。
    它计数临界带 {0 ≤ Re ≤ 1, 0 ≤ Im ≤ T} 中 ξ(z) 的零点数（即 ζ 的非平凡零点数）。 -/
lemma xiZeroCount_eq_NT (T : ℝ) :
    xiZeroCount T = Nat.card {ρ ∈ criticalStrip T | riemannXi ρ = 0} := by
  rfl
