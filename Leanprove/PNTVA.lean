-- Phase V-A: Prime Number Theorem Equivalences
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas
import Leanprove.ZetaIVE

open Chebyshev Asymptotics
open Filter Real
open scoped Topology Nat.Prime

/-!
### Phase V-A: 素数定理 (PNT) 等价形式

素数定理有以下等价表述:
1. ψ(x) ~ x  (第二 Chebyshev 函数)
2. θ(x) ~ x  (第一 Chebyshev 函数)
3. π(x) ~ x / log x  (素数计数函数)

关键工具 (Mathlib):
- |ψ(x) - θ(x)| ≤ 2√x · log(x)  (abs_psi_sub_theta_le_sqrt_mul_log)
- π(⌊x⌋₊) = θ(x)/log(x) + ∫₂ˣ θ(t)/(t·log²t) dt
  (primeCounting_eq_theta_div_log_add_integral)
- ∫₂ˣ θ(t)/(t·log²t) dt = o(x/log x)
  (integral_theta_div_log_sq_isLittleO)
-/


/-! #### 辅助引理 -/

/-- 关键渐近: 2·log x / √x → 0  (x → ∞) -/
private lemma two_log_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => 2 * log x / sqrt x) atTop (nhds 0) := by
  -- log =o[atTop] x^{1/2}  →  2·log =o[atTop] x^{1/2}  →  2·log/x^{1/2} → 0
  have h_log_o_rpow : (fun x : ℝ => log x) =o[atTop] (fun x : ℝ => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h_two_log_o_rpow : (fun x : ℝ => 2 * log x) =o[atTop] (fun x : ℝ => x ^ (1/2 : ℝ)) :=
    h_log_o_rpow.const_mul_left 2
  have h_tendsto := h_two_log_o_rpow.tendsto_div_nhds_zero
  -- Convert x^(1/2) to √x in the denominator (they are equal for x > 0)
  refine h_tendsto.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [sqrt_eq_rpow]

/-- (ψ(x) - θ(x))/x → 0  (Chebyshev 界的关键推论) -/
private lemma psi_sub_theta_div_x_tendsto_zero :
    Tendsto (fun x : ℝ => (ψ x - θ x) / x) atTop (nhds 0) := by
  let bound := fun x : ℝ => 2 * log x / sqrt x
  have h_bound_tendsto : Tendsto bound atTop (nhds 0) := two_log_div_sqrt_tendsto_zero
  have h_neg_tendsto : Tendsto (fun x => -bound x) atTop (nhds 0) := by
    simpa [bound] using h_bound_tendsto.neg
  -- For x ≥ 4: -bound(x) ≤ (ψ x - θ x)/x ≤ bound(x)
  have h_le : ∀ᶠ x in atTop, -bound x ≤ (ψ x - θ x) / x ∧ (ψ x - θ x) / x ≤ bound x := by
    filter_upwards [eventually_ge_atTop 4] with x hx
    have hx1 : 1 ≤ x := by linarith
    have h_pos : 0 < x := by linarith
    have h_sqrt_pos : 0 < sqrt x := sqrt_pos.mpr h_pos
    have h_log_nonneg : 0 ≤ log x := log_nonneg (by linarith)
    have h_bound := abs_psi_sub_theta_le_sqrt_mul_log hx1
    -- |ψ x - θ x| / x ≤ 2·log x / √x  (for x > 0)
    have h_div_bound : |(ψ x - θ x) / x| ≤ bound x := by
      calc |(ψ x - θ x) / x|
        = |ψ x - θ x| / x := by rw [abs_div, abs_of_pos h_pos]
        _ ≤ (2 * sqrt x * log x) / x := by gcongr
        _ = 2 * log x / sqrt x := by
          field_simp [h_pos.ne', h_sqrt_pos.ne']
          rw [mul_comm _ (log x), sq_sqrt (le_of_lt h_pos)]
        _ = bound x := rfl
    -- From |a| ≤ b, get -b ≤ a ≤ b
    have h_upper : (ψ x - θ x) / x ≤ bound x :=
      (le_abs_self _).trans h_div_bound
    have h_lower : -bound x ≤ (ψ x - θ x) / x := by
      -- |a| ≤ b implies -b ≤ a ≤ b
      -- Upper: a ≤ |a| ≤ b
      -- Lower: -a ≤ |-a| = |a| ≤ b, so -b ≤ a
      have h_neg : -(ψ x - θ x) / x ≤ bound x := by
        calc -(ψ x - θ x) / x
          = (θ x - ψ x) / x := by ring
          _ ≤ |(θ x - ψ x) / x| := le_abs_self _
          _ = |(ψ x - θ x) / x| := by
            rw [show (θ x - ψ x) / x = -((ψ x - θ x) / x) by ring, abs_neg]
          _ ≤ bound x := h_div_bound
      -- From -a ≤ b, get -b ≤ a
      -- Help linarith see that -(ψ x - θ x)/x = -((ψ x - θ x)/x)
      have h_neg_eq : -(ψ x - θ x) / x = -((ψ x - θ x) / x) := by ring
      rw [h_neg_eq] at h_neg
      linarith
    exact ⟨h_lower, h_upper⟩
  -- Squeeze theorem: split conjunction into two separate ∀ᶠ statements
  have h_lower_ev : ∀ᶠ x in atTop, -bound x ≤ (ψ x - θ x) / x := by
    filter_upwards [h_le] with x hx
    exact hx.1
  have h_upper_ev : ∀ᶠ x in atTop, (ψ x - θ x) / x ≤ bound x := by
    filter_upwards [h_le] with x hx
    exact hx.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_tendsto h_bound_tendsto
    h_lower_ev h_upper_ev


/-! #### PNT 等价定理 -/

/-- ψ(x)/x → 1 ↔ θ(x)/x → 1 -/
private lemma psi_div_x_iff_theta_div_x :
    Tendsto (fun x : ℝ => ψ x / x) atTop (nhds 1) ↔
    Tendsto (fun x : ℝ => θ x / x) atTop (nhds 1) := by
  have h_diff := psi_sub_theta_div_x_tendsto_zero
  constructor
  · intro hψ
    -- ψ/x → 1 and (ψ-θ)/x → 0, so θ/x = ψ/x - (ψ-θ)/x → 1 - 0 = 1
    have h_sub : Tendsto (fun x => ψ x / x - (ψ x - θ x) / x) atTop (nhds (1 - 0)) :=
      hψ.sub h_diff
    convert h_sub using 1
    · funext x; field_simp; ring
    · norm_num
  · intro hθ
    -- θ/x → 1 and (ψ-θ)/x → 0, so ψ/x = θ/x + (ψ-θ)/x → 1 + 0 = 1
    have h_add : Tendsto (fun x => θ x / x + (ψ x - θ x) / x) atTop (nhds (1 + 0)) :=
      hθ.add h_diff
    convert h_add using 1
    · funext x; field_simp; ring
    · norm_num

/-- IsEquivalent 形式与 Tendsto 形式的转换: u ~ id ↔ u(x)/x → 1 -/
private lemma isEquivalent_id_iff_tendsto_div_one {u : ℝ → ℝ}
    (h_zero : u 0 = 0) :
    u ~[atTop] (fun x : ℝ => x) ↔
    Tendsto (fun x => u x / x) atTop (nhds 1) := by
  constructor
  · -- u ~ id → u(x)/x → 1
    intro h
    have h_div := h.isLittleO.tendsto_div_nhds_zero
    have h_eq : (fun x => (u x - x) / x) =ᶠ[atTop]
        (fun x => u x / x - 1) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp [hx.ne']
    have h_sub : Tendsto (fun x => u x / x - 1) atTop (nhds 0) :=
      Tendsto.congr' h_eq h_div
    convert h_sub.add (tendsto_const_nhds (x := (1 : ℝ))) using 1
    · funext x; ring
    · norm_num
  · -- u(x)/x → 1 → u ~ id
    intro h
    have h_eq : (fun x => u x / x - 1) =ᶠ[atTop]
        (fun x => (u x - x) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp [hx.ne']
    -- u(x)/x - 1 → 1 - 1 = 0
    have h_sub_tendsto : Tendsto (fun x => u x / x - 1) atTop (nhds (1 - 1)) :=
      h.sub (tendsto_const_nhds (x := (1 : ℝ)))
    -- Since (1 : ℝ) - 1 = 0, we can replace the target
    have h_zero_eq : (1 : ℝ) - 1 = 0 := by norm_num
    have h_sub_tendsto' : Tendsto (fun x => u x / x - 1) atTop (nhds 0) :=
      h_zero_eq ▸ h_sub_tendsto
    have h_div : Tendsto (fun x => (u x - x) / x) atTop (nhds 0) :=
      Tendsto.congr' h_eq h_sub_tendsto'
    have h_zero_cond : ∀ x : ℝ, x = 0 → u x - x = 0 := by
      intro x hx; simp [hx, h_zero]
    exact (isLittleO_iff_tendsto h_zero_cond).mpr h_div

/-- PNT 等价: ψ(x) ~ x ↔ θ(x) ~ x -/
theorem pnt_psi_iff_pnt_theta :
    ψ ~[atTop] (fun x : ℝ => x) ↔ θ ~[atTop] (fun x : ℝ => x) := by
  have h_psi : ψ ~[atTop] (fun x : ℝ => x) ↔
      Tendsto (fun x => ψ x / x) atTop (nhds 1) :=
    isEquivalent_id_iff_tendsto_div_one (by simp [psi])
  have h_theta : θ ~[atTop] (fun x : ℝ => x) ↔
      Tendsto (fun x => θ x / x) atTop (nhds 1) :=
    isEquivalent_id_iff_tendsto_div_one (by simp [theta])
  rw [h_psi, h_theta]
  exact psi_div_x_iff_theta_div_x

/-! #### PNT 等价: θ(x) ~ x ↔ π(x) ~ x/log x -/

/-- 辅助: x/log²x =o[atTop] x/log x -/
private lemma x_div_log_sq_isLittleO_x_div_log :
    (fun x : ℝ => x / log x ^ 2) =o[atTop] (fun x : ℝ => x / log x) := by
  have h_zero_cond : ∀ x : ℝ, x / log x = 0 → x / log x ^ 2 = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hl : log x = 0
      · have : log x ^ 2 = 0 := by simp [hl]
        simp [this]
      · have h : x = x / log x * log x := by field_simp [hx0, hl]
        rw [hx, zero_mul] at h
        contradiction
  refine (isLittleO_iff_tendsto h_zero_cond).mpr ?_
  -- (x/log²x) / (x/log x) = 1/log x = (log x)⁻¹ → 0
  refine Tendsto.congr' (f₁ := fun x : ℝ => (log x)⁻¹) ?_
    tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hx0 : x ≠ 0 := by linarith
  have h_log_ne : log x ≠ 0 := (log_pos hx).ne'
  field_simp [hx0, h_log_ne, inv_eq_one_div]

/-- 辅助: π ~ θ/log  (Abel 求和的推论) -/
private lemma pi_isEquivalent_theta_div_log :
    (fun x : ℝ => (π ⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => θ x / log x) := by
  -- π - θ/log = O(x/log²x) and x/log²x =o(θ/log) → π - θ/log =o(θ/log) → π ~ θ/log
  have h_bigO := primeCounting_sub_theta_div_log_isBigO
  have h_littleO_of_bound := x_div_log_sq_isLittleO_x_div_log
  have h_diff_isLittleO :
      (fun x : ℝ => (π ⌊x⌋₊ : ℝ) - θ x / log x) =o[atTop] (fun x : ℝ => x / log x) :=
    h_bigO.trans_isLittleO h_littleO_of_bound
  -- Key: show x/log²x =o(θ/log) via Chebyshev lower bound on θ
  -- Chebyshev lower bound: ∃ c > 0, eventually c·x ≤ θ x
  -- From theta_ge': θ x ≥ (x-1)·log 2 - log(x+2) - 2√x·log x
  -- Since 2√x·log x = o(x) and log(x+2) = o(x), we get θ x ≥ c·x for c = log 2/4
  have h_theta_lower : ∃ c > 0, ∀ᶠ x : ℝ in atTop, c * x ≤ θ x := by
    use log 2 / 4
    constructor
    · apply div_pos; exact log_pos (by norm_num); norm_num
    · -- 2√x·log x = o(x): ratio 2log x/√x → 0 (already proved)
      have h_sqrtlog_o : (fun x : ℝ => 2 * sqrt x * log x) =o[atTop] (fun x => x) := by
        refine (isLittleO_iff_tendsto' ?_).mpr ?_
        · filter_upwards [eventually_gt_atTop 0] with x hx
          intro hx0
          have : sqrt x ≠ 0 := (sqrt_pos.mpr hx).ne'
          have : x ≠ 0 := hx.ne'
          simp_all
        · refine Tendsto.congr' (f₁ := fun x => 2 * log x / sqrt x) ?_ two_log_div_sqrt_tendsto_zero
          filter_upwards [eventually_gt_atTop 0] with x hx
          have h_sqrt_ne : sqrt x ≠ 0 := (sqrt_pos.mpr hx).ne'
          field_simp [hx.ne', h_sqrt_ne]
          rw [sq_sqrt (le_of_lt hx)]
      -- log(x+2) = o(x): compose log =o(id) with (x ↦ x+2), then x+2 =O(x)
      have h_logx2_o : (fun x : ℝ => log (x + 2)) =o[atTop] (fun x => x) := by
        have h_log_o_id : (fun x : ℝ => log x) =o[atTop] (fun x => x) := by
          simpa [rpow_one] using isLittleO_log_rpow_atTop (r := 1) (by norm_num)
        have h1 : (fun x : ℝ => log (x + 2)) =o[atTop] (fun x => x + 2) :=
          h_log_o_id.comp_tendsto (Tendsto.atTop_add tendsto_id tendsto_const_nhds)
        have h2 : (fun x : ℝ => x + 2) =O[atTop] (fun x => x) := by
          refine IsBigO.of_bound 2 ?_
          filter_upwards [eventually_ge_atTop 2] with x hx
          have hx_pos : 0 < x := by linarith
          simp [abs_of_pos hx_pos, abs_of_pos (show 0 < x + 2 by linarith)]
          linarith
        exact h1.trans_isBigO h2
      -- Get epsilon bounds (IsLittleO.bound gives ‖·‖ form)
      have h_eps := h_sqrtlog_o.bound (show 0 < log 2 / 4 by
        apply div_pos; exact log_pos (by norm_num); norm_num)
      have h_eps2 := h_logx2_o.bound (show 0 < log 2 / 4 by
        apply div_pos; exact log_pos (by norm_num); norm_num)
      filter_upwards [eventually_ge_atTop 4, h_eps, h_eps2] with x hx h_sqrtlog_bound h_logx2_bound
      have h_ge := theta_ge' (by linarith : (1 : ℝ) ≤ x)
      have h_log2_pos : 0 < log 2 := log_pos (by norm_num)
      have hx_pos : 0 < x := by linarith
      have h_sqrtlog_pos : 0 ≤ 2 * sqrt x * log x := by
        apply mul_nonneg; apply mul_nonneg; norm_num
        exact sqrt_nonneg x; exact log_nonneg (by linarith)
      have h_logx2_pos : 0 ≤ log (x + 2) := log_nonneg (by linarith)
      -- Simplify norms to actual values
      have h_sqrtlog_le : 2 * sqrt x * log x ≤ (log 2 / 4) * x := by
        rw [Real.norm_eq_abs, abs_of_nonneg h_sqrtlog_pos, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)] at h_sqrtlog_bound
        exact h_sqrtlog_bound
      have h_logx2_le : log (x + 2) ≤ (log 2 / 4) * x := by
        rw [Real.norm_eq_abs, abs_of_nonneg h_logx2_pos, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)] at h_logx2_bound
        exact h_logx2_bound
      -- Combine: θ x ≥ (log 2/4)·x
      calc (log 2 / 4) * x
        ≤ (log 2 / 2) * x - log 2 := by nlinarith [h_log2_pos]
        _ ≤ (x - 1) * log 2 - log (x + 2) - 2 * sqrt x * log x := by
          nlinarith [h_logx2_le, h_sqrtlog_le]
        _ ≤ θ x := h_ge
  -- Destructure the existential for use in subsequent proofs
  obtain ⟨c_theta, hc_pos, h_theta_lower_ev⟩ := h_theta_lower
  -- x/log²x =o(θ/log): ratio = (x·log x)/(log²x·θ x) → 0
  have h_xlog2_o_theta_log :
      (fun x : ℝ => x / log x ^ 2) =o[atTop] (fun x : ℝ => θ x / log x) := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · -- The zero condition: ∀ᶠ x, θ x / log x = 0 → x / log²x = 0
      filter_upwards [eventually_gt_atTop 2, h_theta_lower_ev] with x hx hθ_low
      intro h_zero
      have h_log_pos : 0 < log x := log_pos (by linarith)
      have h_theta_pos : 0 < θ x := by
        have : 0 < c_theta * x := mul_pos hc_pos (by linarith)
        linarith
      have h_denom_pos : 0 < θ x / log x := div_pos h_theta_pos h_log_pos
      linarith
    · -- The ratio → 0: use squeeze theorem
      have h_bound : ∀ᶠ x : ℝ in atTop,
          0 ≤ (x / log x ^ 2) / (θ x / log x) ∧
          (x / log x ^ 2) / (θ x / log x) ≤ 1 / (c_theta * log x) := by
        filter_upwards [eventually_gt_atTop 4, h_theta_lower_ev] with x hx hθ_low
        have h_log_pos : 0 < log x := log_pos (by linarith)
        have h_theta_pos : 0 < θ x := by
          have : 0 < c_theta * x := mul_pos hc_pos (by linarith)
          linarith
        have h_x_pos : 0 < x := by linarith
        have h_num_pos : 0 < x / log x ^ 2 := div_pos h_x_pos (sq_pos_of_pos h_log_pos)
        have h_den_pos : 0 < θ x / log x := div_pos h_theta_pos h_log_pos
        constructor
        · exact div_nonneg h_num_pos.le h_den_pos.le
        · -- Upper bound: θ x ≥ c_theta·x → ratio ≤ 1/(c_theta·log x)
          have h_ratio_eq : (x / log x ^ 2) / (θ x / log x) =
              (x * log x) / (log x ^ 2 * θ x) := by
            field_simp [h_x_pos.ne', h_log_pos.ne', h_theta_pos.ne']
          have h_bound_val : (x * log x) / (log x ^ 2 * θ x) ≤
              (x * log x) / (log x ^ 2 * (c_theta * x)) := by
            have h_num_nonneg : 0 ≤ x * log x := by
              apply mul_nonneg; linarith; exact le_of_lt h_log_pos
            have h_den1_pos : 0 < log x ^ 2 * θ x := by
              apply mul_pos; exact sq_pos_of_pos h_log_pos; exact h_theta_pos
            have h_den2_pos : 0 < log x ^ 2 * (c_theta * x) := by
              apply mul_pos; exact sq_pos_of_pos h_log_pos
              apply mul_pos; exact hc_pos; linarith
            refine (div_le_div_iff₀ h_den1_pos h_den2_pos).mpr ?_
            -- (x*log x) * (log²x * c_theta * x) ≤ (x*log x) * (log²x * θ x)
            apply mul_le_mul_of_nonneg_left _ h_num_nonneg
            apply mul_le_mul_of_nonneg_left hθ_low (sq_nonneg (log x))
          have h_simplify : (x * log x) / (log x ^ 2 * (c_theta * x)) =
              1 / (c_theta * log x) := by
            field_simp [h_x_pos.ne', h_log_pos.ne', hc_pos.ne']
          calc (x / log x ^ 2) / (θ x / log x)
            = (x * log x) / (log x ^ 2 * θ x) := h_ratio_eq
            _ ≤ (x * log x) / (log x ^ 2 * (c_theta * x)) := h_bound_val
            _ = 1 / (c_theta * log x) := h_simplify
      -- Now show both bounds tend to 0
      have h_zero_tendsto : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
      have h_upper_tendsto : Tendsto (fun x : ℝ => 1 / (c_theta * log x)) atTop (nhds 0) := by
        -- 1/(c_theta · log x) = (1/c_theta) / log x → 0 since log x → ∞
        have h_eq : (fun x : ℝ => 1 / (c_theta * log x)) =ᶠ[atTop]
            (fun x : ℝ => (1 / c_theta) / log x) := by
          filter_upwards [eventually_gt_atTop 1] with x hx
          have h_log_ne : log x ≠ 0 := (log_pos (by linarith)).ne'
          field_simp [hc_pos.ne', h_log_ne]
        have h_tendsto : Tendsto (fun x : ℝ => (1 / c_theta) / log x) atTop (nhds 0) :=
          tendsto_log_atTop.const_div_atTop (1 / c_theta)
        exact Tendsto.congr' h_eq.symm h_tendsto
      have h_lower_ev : ∀ᶠ x in atTop, 0 ≤ (x / log x ^ 2) / (θ x / log x) := by
        filter_upwards [h_bound] with x hx; exact hx.1
      have h_upper_ev : ∀ᶠ x in atTop,
          (x / log x ^ 2) / (θ x / log x) ≤ 1 / (c_theta * log x) := by
        filter_upwards [h_bound] with x hx; exact hx.2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        h_zero_tendsto h_upper_tendsto h_lower_ev h_upper_ev
  -- Compose: (π - θ/log) = O(x/log²x) and x/log²x =o(θ/log) → (π - θ/log) =o(θ/log)
  have h_diff_o : (fun x : ℝ => (π ⌊x⌋₊ : ℝ) - θ x / log x) =o[atTop]
      (fun x : ℝ => θ x / log x) :=
    h_bigO.trans_isLittleO h_xlog2_o_theta_log
  -- θ/log + (π - θ/log) ~ θ/log  (add_isLittleO with refl)
  have h_add_equiv : (fun x : ℝ => θ x / log x + ((π ⌊x⌋₊ : ℝ) - θ x / log x))
      ~[atTop] (fun x : ℝ => θ x / log x) :=
    IsEquivalent.add_isLittleO (IsEquivalent.refl) h_diff_o
  -- θ/log + (π - θ/log) = π (algebraic identity)
  have h_sum_eq : (fun x : ℝ => θ x / log x + ((π ⌊x⌋₊ : ℝ) - θ x / log x))
      =ᶠ[atTop] (fun x : ℝ => (π ⌊x⌋₊ : ℝ)) := by
    filter_upwards with x; ring
  -- Combine: π = θ/log + (π - θ/log) ~ θ/log → π ~ θ/log
  exact (h_add_equiv.symm.trans_eventuallyEq h_sum_eq).symm

/-- PNT 等价: θ(x) ~ x ↔ π(x) ~ x/log x -/
theorem pnt_theta_iff_pnt_pi :
    θ ~[atTop] (fun x : ℝ => x) ↔
    (fun x : ℝ => (π ⌊x⌋₊ : ℝ) / (x / log x)) ~[atTop] fun _ : ℝ => (1 : ℝ) := by
  have h_pi_equiv := pi_isEquivalent_theta_div_log
  -- Key conversion: θ ~ x ↔ Tendsto (θ(x)/x) atTop (𝓝 1)
  have h_theta_iff :
      (θ ~[atTop] (fun x : ℝ => x)) ↔
      Tendsto (fun x => θ x / x) atTop (nhds 1) :=
    isEquivalent_id_iff_tendsto_div_one (by simp [theta])
  -- Key conversion: (π/(x/log x)) ~ 1 ↔ Tendsto (π/(x/log x)) atTop (𝓝 1)
  have h_nz_xlog : ∀ᶠ x : ℝ in atTop, x / log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_ne_zero (by linarith) (log_pos (by linarith)).ne'
  -- θ/log ~ x/log ↔ Tendsto ((θ/log)/(x/log)) atTop (𝓝 1) ↔ Tendsto (θ/x) atTop (𝓝 1)
  have h_theta_log_iff :
      ((fun x => θ x / log x) ~[atTop] (fun x => x / log x)) ↔
      Tendsto (fun x => θ x / x) atTop (nhds 1) := by
    constructor
    · intro h
      have h_eq : (fun x => (θ x / log x) / (x / log x)) =ᶠ[atTop]
          (fun x => θ x / x) := by
        filter_upwards [eventually_gt_atTop 1] with x hx
        have h_log_ne : log x ≠ 0 := (log_pos (by linarith)).ne'
        have h_x_ne : x ≠ 0 := by linarith
        field_simp [h_log_ne, h_x_ne]
      exact Tendsto.congr' h_eq ((isEquivalent_iff_tendsto_one h_nz_xlog).mp h)
    · intro h
      have h_eq : (fun x => θ x / x) =ᶠ[atTop]
          (fun x => (θ x / log x) / (x / log x)) := by
        filter_upwards [eventually_gt_atTop 1] with x hx
        have h_log_ne : log x ≠ 0 := (log_pos (by linarith)).ne'
        have h_x_ne : x ≠ 0 := by linarith
        field_simp [h_log_ne, h_x_ne]
      exact (isEquivalent_iff_tendsto_one h_nz_xlog).mpr (Tendsto.congr' h_eq h)
  constructor
  · -- Forward: θ ~ x → (π/(x/log x)) ~ 1
    intro hθ
    -- θ ~ x → θ/log ~ x/log
    have h_theta_log := h_theta_log_iff.mpr (h_theta_iff.mp hθ)
    -- π ~ θ/log → π ~ x/log
    have h_pi_xlog : (fun x => (π ⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x / log x) :=
      h_pi_equiv.trans h_theta_log
    -- π ~ x/log → Tendsto (π/(x/log x)) atTop (𝓝 1)
    have h_tendsto := (isEquivalent_iff_tendsto_one h_nz_xlog).mp h_pi_xlog
    -- Tendsto (π/(x/log x)) atTop (𝓝 1) → (π/(x/log x)) ~ 1
    let f : ℝ → ℝ := fun x => (π ⌊x⌋₊ : ℝ) / (x / log x)
    -- f ~ 1 ↔ (f - 1) =o[atTop] 1 ↔ f - 1 → 0 ↔ f → 1
    have h_one_iff :
        (f ~[atTop] fun _ : ℝ => (1 : ℝ)) ↔
        Tendsto f atTop (nhds 1) := by
      constructor
      · intro h
        have h_o : (fun x => f x - 1) =o[atTop] (fun _ : ℝ => (1 : ℝ)) := h
        have h_sub := (isLittleO_const_iff one_ne_zero).mp h_o
        convert h_sub.add (tendsto_const_nhds (x := (1 : ℝ))) using 1
        · funext x; ring
        · norm_num
      · intro hf
        have h_sub : Tendsto (fun x => f x - 1) atTop (nhds (1 - 1)) :=
          hf.sub (tendsto_const_nhds (x := (1 : ℝ)))
        exact (isLittleO_const_iff one_ne_zero).mpr ((show (1 : ℝ) - 1 = 0 by norm_num) ▸ h_sub)
    exact h_one_iff.mpr h_tendsto
  · -- Backward: (π/(x/log x)) ~ 1 → θ ~ x
    intro hpi_one
    -- (π/(x/log x)) ~ 1 → Tendsto (π/(x/log x)) atTop (𝓝 1)
    let f : ℝ → ℝ := fun x => (π ⌊x⌋₊ : ℝ) / (x / log x)
    have h_one_iff :
        (f ~[atTop] fun _ : ℝ => (1 : ℝ)) ↔
        Tendsto f atTop (nhds 1) := by
      constructor
      · intro h
        have h_o : (fun x => f x - 1) =o[atTop] (fun _ : ℝ => (1 : ℝ)) := h
        have h_sub := (isLittleO_const_iff one_ne_zero).mp h_o
        convert h_sub.add (tendsto_const_nhds (x := (1 : ℝ))) using 1
        · funext x; ring
        · norm_num
      · intro hf
        have h_sub : Tendsto (fun x => f x - 1) atTop (nhds (1 - 1)) :=
          hf.sub (tendsto_const_nhds (x := (1 : ℝ)))
        exact (isLittleO_const_iff one_ne_zero).mpr ((show (1 : ℝ) - 1 = 0 by norm_num) ▸ h_sub)
    have hpi_tendsto := h_one_iff.mp hpi_one
    -- Tendsto (π/(x/log x)) atTop (𝓝 1) → π ~ x/log
    have h_pi_xlog : (fun x => (π ⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x / log x) :=
      (isEquivalent_iff_tendsto_one h_nz_xlog).mpr hpi_tendsto
    -- π ~ x/log → θ/log ~ x/log (via h_pi_equiv.symm)
    have h_theta_log := h_pi_equiv.symm.trans h_pi_xlog
    -- θ/log ~ x/log → Tendsto (θ/x) atTop (𝓝 1) → θ ~ x
    exact h_theta_iff.mpr (h_theta_log_iff.mp h_theta_log)

/-- PNT 等价: ψ(x) ~ x ↔ π(x) ~ x/log x (传递性) -/
theorem pnt_psi_iff_pnt_pi :
    ψ ~[atTop] (fun x : ℝ => x) ↔
    (fun x : ℝ => (π ⌊x⌋₊ : ℝ) / (x / log x)) ~[atTop] fun _ : ℝ => (1 : ℝ) := by
  rw [pnt_psi_iff_pnt_theta, pnt_theta_iff_pnt_pi]


/-! #### ζ 函数对数导数恒等式 (包装 mathlib) -/

open ArithmeticFunction in

/-- -ζ'(s)/ζ(s) = ∑ Λ(n)/n^s 对 Re(s) > 1 (对数导数公式) -/
theorem log_deriv_zeta_eq_vonMangoldt_series (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) s := by
  -- Direct wrapper around mathlib's LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  refine (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm.trans ?_
  refine LSeries_congr (fun {n} hn => ?_) s
  simp

/-- -ζ'(s)/ζ(s) 在 {Re(s) ≥ 1} \ {1} 上全纯
    (由 ζ(s) ≠ 0 和解析性; s=1 处有简单极点) -/
theorem log_deriv_zeta_analytic :
    AnalyticOnNhd ℂ (fun s => -deriv riemannZeta s / riemannZeta s)
      {s : ℂ | 1 ≤ s.re ∧ s ≠ 1} := by
  let S : Set ℂ := {s | 1 ≤ s.re ∧ s ≠ 1}
  have hS : S ⊆ {1}ᶜ := fun s hs => hs.2
  have hζ := analyticOn_riemannZeta.mono hS
  have hζ' := analyticOn_riemannZeta.deriv.mono hS
  have hne : ∀ s ∈ S, riemannZeta s ≠ 0 := fun s hs =>
    riemannZeta_ne_zero_of_one_le_re hs.1
  exact (hζ'.neg.div hζ hne)


/-! #### 素数定理 (陈述，待证) -/

/-- **素数定理** (第二 Chebyshev 形式): ψ(x) ~ x
    证明需要 Tauberian 定理 (Wiener-Ikehara / Newman)，mathlib 中尚未实现。-/
theorem prime_number_theorem_psi :
    ψ ~[atTop] (fun x : ℝ => x) := by
  sorry

/-- **素数定理** (标准形式): π(x) ~ x / log x -/
theorem prime_number_theorem_pi :
    (fun x : ℝ => (π ⌊x⌋₊ : ℝ) / (x / log x)) ~[atTop] fun _ : ℝ => (1 : ℝ) := by
  sorry
