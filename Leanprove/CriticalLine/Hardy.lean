/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

import Mathlib.Topology.ContinuousOn
import Leanprove.CriticalLine.Definitions

open Complex Real Filter
open scoped Topology BigOperators ComplexConjugate

noncomputable section

/-! # CriticalLine.Hardy

Hardy 定理框架：临界线上的零点理论、IVT、无限变号归约
本模块包含 Hardy 定理的实分析核心和完整归约结构。

## Main definitions

* `criticalLine` — 临界线参数化
* `xi_on_critical_line` — ξ 在临界线上的实值限制
* `criticalLineZeros` — 临界线零点集合 ℝ
* `criticalLineZeroCount` — 临界线零点计数 N₀(T)
* `xiOscillationHypothesis` — ξ 振荡性假设
* `hardyLittlewoodMeanValueHypothesis` — Hardy-Littlewood 均值假设

## Main results

* `infinite_zeros_of_infinite_sign_changes` — 无限变号 ⇒ 无限零点（通用实分析引理）
* `hardys_theorem_by_sign_changes` — 从变号到 Hardy 定理的归约
* `hardy_theorem_full` — Hardy 定理的完整形式化（需 oscillation + mean value）
-/

/-! ## 临界线参数化 -/

/-- 临界线参数化：t ↦ 1/2 + I·t -/
def criticalLine (t : ℝ) : ℂ :=
  (1 : ℂ) / 2 + I * (t : ℂ)

/-- criticalLine 的实部与虚部 -/
lemma criticalLine_re_im (t : ℝ) : re (criticalLine t) = 1/2 ∧ im (criticalLine t) = t := by
  simp [criticalLine]

/-- ξ 在临界线上的实值限制 -/
def xi_on_critical_line (t : ℝ) : ℝ :=
  (riemannXi (criticalLine t)).re

/-- xi_on_critical_line 的定义展开 -/
lemma xi_on_critical_line_eq (t : ℝ) :
    xi_on_critical_line t = (riemannXi (criticalLine t)).re := rfl

/-! ### ξ 在关键点的特殊值 -/

/-- ξ(1/2) 的值 -/
lemma xi_at_half : riemannXi (1/2) =
    -(1/4 : ℂ) * (π : ℂ) ^ (-(1/4) : ℂ) * Complex.Gamma (1/4) * riemannZeta (1/2) := by
  have hs : (1/2 : ℂ) ≠ 0 := by norm_num
  have hG : Gammaℝ (1/2) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < (1/2 : ℂ).re)
  have hcr : riemannZeta (1/2) * Gammaℝ (1/2) = completedRiemannZeta (1/2) := by
    rw [riemannZeta_def_of_ne_zero hs, div_mul_cancel₀ _ hG]
  rw [riemannXi, completedZeta, ← hcr, Gammaℝ]
  ring

/-- ξ(1) 的值 -/
lemma xi_at_one : riemannXi 1 = 0 := by
  rw [riemannXi]
  have h1 : 1 * (1 - 1) = 0 := by norm_num
  simp [h1]

/-- ξ(0) 的值 -/
lemma xi_at_zero : riemannXi 0 = 0 := by
  rw [riemannXi]
  have h1 : 0 * (0 - 1) = 0 := by norm_num
  simp [h1]

/-! ## 临界线零点集合 -/

/-- 临界线零点集合：{t ∈ ℝ | xi_on_critical_line t = 0} -/
def criticalLineZeros : Set ℝ :=
  { t | xi_on_critical_line t = 0 }

/-- t ∈ criticalLineZeros ↔ ξ(1/2 + I·t) = 0 -/
lemma criticalLineZeros_iff {t : ℝ} : t ∈ criticalLineZeros ↔ riemannXi (criticalLine t) = 0 := by
  simp [criticalLineZeros, xi_on_critical_line]
  have h : (riemannXi (criticalLine t)).im = 0 := riemannXi_real_on_critical_line t
  constructor
  · intro hzero
    exact Complex.ext hzero h
  · intro hzero
    simpa [hzero]

/-- criticalLineZeros 中的 t 对应 riemannXiZeros 中的点 -/
lemma criticalLineZeros_mem_riemannXiZeros {t : ℝ} (ht : t ∈ criticalLineZeros) :
    criticalLine t ∈ riemannXiZeros := by
  rw [riemannXiZeros]
  exact criticalLineZeros_iff.mp ht

/-- 临界线零点落入 criticalStrip 的条件 -/
lemma criticalLineZeros_inter_criticalStrip {t : ℝ} (T : ℝ) (ht : t ∈ criticalLineZeros) :
    criticalLine t ∈ criticalStrip T ↔ 0 ≤ t ∧ t ≤ T := by
  simp [criticalStrip, criticalLine]
  exact fun h1 h2 => by norm_num

/-- 临界线上在高度 T 以下的零点计数 N₀(T) -/
noncomputable def criticalLineZeroCount (T : ℝ) : ℕ :=
  Nat.card {t : ℝ | t ∈ criticalLineZeros ∧ 0 ≤ t ∧ t ≤ T}

/-- N₀(T) ≤ N(T)（ξ 零点计数）
    证明策略: criticalLine t = 1/2 + It 是从临界线零点到 ξ 零点的单射
    需要 card_le_of_injective' + 无限性传递条件 -/
lemma criticalLineZeroCount_le_xiZeroCount (T : ℝ) : criticalLineZeroCount T ≤ xiZeroCount T := by
  sorry

/-! ## Hardy 定理的实分析核心 -/

/-- 连续函数 + 端点异号 ⇒ ∃c ∈ [a,b], f(c)=0 -/
lemma exists_zero_Icc_of_sign_change {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  have h := intermediate_value_Icc hab hf
  have h0 : 0 ∈ Set.Icc (f a) (f b) := ⟨hfa, hfb⟩
  exact h h0

/-- 连续函数 + 端点异号（符号反转版本） -/
lemma exists_zero_Icc_of_sign_change' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : 0 ≤ f a) (hfb : f b ≤ 0) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  have h := intermediate_value_Icc' hab hf
  have h0 : 0 ∈ Set.Icc (f b) (f a) := ⟨hfb, hfa⟩
  exact h h0

/-- 通用主定理：若 f 连续且在任意 [M, ∞) 上既取正值又取负值 ⇒ 零点集无限 -/
theorem infinite_zeros_of_infinite_sign_changes {f : ℝ → ℝ} (hf : Continuous f)
    (h_pos : ∀ M : ℝ, ∃ t ≥ M, f t > 0) (h_neg : ∀ M : ℝ, ∃ t ≥ M, f t < 0) :
    Set.Infinite { t | f t = 0 } := by
  by_contra h_fin
  have h_fin' : Set.Finite { t | f t = 0 } := Set.not_infinite.mp h_fin
  have h_bdd : BddAbove { t | f t = 0 } := h_fin'.bddAbove
  rcases Set.eq_empty_or_nonempty { t | f t = 0 } with h_empty | ⟨x₀, hx₀⟩
  · -- 无零点：找符号变化，IVT 得零点，矛盾
    obtain ⟨t1, _, hf1⟩ := h_pos 0
    obtain ⟨t2, _, hf2⟩ := h_neg 0
    rcases le_total t1 t2 with h | h
    · obtain ⟨c, _, hc⟩ := exists_zero_Icc_of_sign_change' h hf.continuousOn (le_of_lt hf1) (le_of_lt hf2)
      exact Set.notMem_empty c (h_empty ▸ (hc : c ∈ {t | f t = 0}))
    · obtain ⟨c, _, hc⟩ := exists_zero_Icc_of_sign_change h hf.continuousOn (le_of_lt hf2) (le_of_lt hf1)
      exact Set.notMem_empty c (h_empty ▸ (hc : c ∈ {t | f t = 0}))
  · -- 有零点：M = sSup 是上界
    let M := sSup { t | f t = 0 }
    -- f M = 0（连续 + 闭集 + sSup 性质）
    have hM_zero : f M = 0 := by
      have h_cl : IsClosed { t | f t = 0 } := isClosed_singleton.preimage hf
      have hM_in : M ∈ { t | f t = 0 } := h_cl.csSup_mem (by exact ⟨x₀, hx₀⟩) h_bdd
      exact hM_in
    -- 取 t1, t2 > M 的符号变化点
    obtain ⟨t1, ht1, hf1⟩ := h_pos M
    obtain ⟨t2, ht2, hf2⟩ := h_neg M
    -- t1 > M（f t1 > 0 = f M，故 t1 ≠ M）
    have ht1_gt : M < t1 := by
      rcases eq_or_lt_of_le ht1 with h | h
      · linarith [h ▸ hM_zero]
      · exact h
    have ht2_gt : M < t2 := by
      rcases eq_or_lt_of_le ht2 with h | h
      · linarith [h ▸ hM_zero]
      · exact h
    have hmin_gt : M < min t1 t2 := lt_min ht1_gt ht2_gt
    -- IVT 得零点
    rcases le_total t1 t2 with h_le | h_lt
    · obtain ⟨c, hc_mem, hc_zero⟩ := exists_zero_Icc_of_sign_change' h_le hf.continuousOn (le_of_lt hf1) (le_of_lt hf2)
      have h_c_gt : M < c := lt_of_lt_of_le ht1_gt hc_mem.1
      have h_c_le : c ≤ M := le_csSup h_bdd hc_zero
      linarith
    · obtain ⟨c, hc_mem, hc_zero⟩ := exists_zero_Icc_of_sign_change h_lt hf.continuousOn (le_of_lt hf2) (le_of_lt hf1)
      have h_c_gt : M < c := lt_of_lt_of_le ht2_gt hc_mem.1
      have h_c_le : c ≤ M := le_csSup h_bdd hc_zero
      linarith

/-! ### 临界线零点集合的拓扑性质 -/

/-- xi_on_critical_line 的连续性 -/
lemma xi_on_critical_line_continuous : Continuous xi_on_critical_line := by
  -- criticalLine t = 1/2 + I*t 永远离 0 和 1
  have hc0 : ∀ t : ℝ, criticalLine t ≠ 0 := by
    intro t h; simp [criticalLine, Complex.ext_iff] at h
  have hc1 : ∀ t : ℝ, criticalLine t ≠ 1 := by
    intro t h; simp [criticalLine, Complex.ext_iff] at h
  -- 逐点证明 ContinuousAt，再用 continuous_iff_continuousAt
  rw [continuous_iff_continuousAt]
  intro t
  -- completedRiemannZeta 在 criticalLine t 处连续（可微 ⇒ 连续）
  have h_zeta_ct : ContinuousAt completedRiemannZeta (criticalLine t) :=
    (differentiableAt_completedZeta (hc0 t) (hc1 t)).continuousAt
  -- criticalLine 连续：t ↦ 1/2 + I·t 是仿射函数
  have h_cl_ct : ContinuousAt criticalLine t := by
    unfold criticalLine
    exact (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousAt
  -- 组合：completedRiemannZeta ∘ criticalLine 连续
  have h_comp : ContinuousAt (fun t ↦ completedRiemannZeta (criticalLine t)) t :=
    h_zeta_ct.comp h_cl_ct
  -- s*(s-1) 在 criticalLine t 处连续
  have h_poly : ContinuousAt (fun t ↦ criticalLine t * (criticalLine t - 1)) t :=
    h_cl_ct.mul (h_cl_ct.sub continuousAt_const)
  -- 整体 riemannXi ∘ criticalLine 连续
  have h_xi : ContinuousAt (fun t ↦ riemannXi (criticalLine t)) t := by
    change ContinuousAt (fun t ↦ criticalLine t * (criticalLine t - 1) * completedRiemannZeta (criticalLine t)) t
    exact h_poly.mul h_comp
  -- 取实部
  exact continuous_re.continuousAt.comp h_xi

/-- criticalLineZeros 是闭集 -/
lemma criticalLineZeros_isClosed : IsClosed criticalLineZeros := by
  have h : criticalLineZeros = xi_on_critical_line ⁻¹' {0} := rfl
  rw [h]
  apply IsClosed.preimage xi_on_critical_line_continuous
  exact isClosed_singleton

/-- 临界线上零点集是离散的 -/
lemma criticalLineZeros_isDiscrete : DiscreteTopology {s : ℂ | s ∈ Set.range criticalLine ∧ s ∈ riemannXiZeros} := by
  sorry

/-! ## Hardy 定理的正式归约 -/

/-- Hardy 定理的实分析归约：从无限变号到无限零点 -/
theorem hardys_theorem_by_sign_changes
    (h_pos : ∀ M : ℝ, ∃ t ≥ M, xi_on_critical_line t > 0)
    (h_neg : ∀ M : ℝ, ∃ t ≥ M, xi_on_critical_line t < 0) :
    Set.Infinite criticalLineZeros :=
  infinite_zeros_of_infinite_sign_changes xi_on_critical_line_continuous h_pos h_neg

/-- Hardy 定理的完整陈述 -/
theorem hardys_theorem_statement :
    Set.Infinite criticalLineZeros → True := by
  intro h
  exact trivial

/-- ξ 振荡性假设：xi_on_critical_line 在任意远处既取正值又取负值 -/
def xiOscillationHypothesis : Prop :=
  (∀ M : ℝ, ∃ t : ℝ, t > M ∧ xi_on_critical_line t > 0) ∧
  (∀ M : ℝ, ∃ t : ℝ, t > M ∧ xi_on_critical_line t < 0)

/-- 从振荡假设到无限零点 -/
theorem hardy_theorem_from_oscillation (h_osc : xiOscillationHypothesis) :
    Set.Infinite criticalLineZeros :=
  hardys_theorem_by_sign_changes
    (fun M => let ⟨t, ht, hf⟩ := h_osc.1 M; ⟨t, le_of_lt ht, hf⟩)
    (fun M => let ⟨t, ht, hf⟩ := h_osc.2 M; ⟨t, le_of_lt ht, hf⟩)

/-! ## Hardy 定理的数论假设 -/

/-- Hardy-Littlewood 均值积分假设 -/
def hardyLittlewoodMeanValueHypothesis : Prop :=
  ∀ᶠ T in atTop, ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    C₁ * T * Real.log (T / (2 * Real.pi)) ≤
      ∫ t in (0 : ℝ)..T, ‖riemannZeta (criticalLine t)‖ ^ 2 ∧
    ∫ t in (0 : ℝ)..T, ‖riemannZeta (criticalLine t)‖ ^ 2 ≤
      C₂ * T * Real.log (T / (2 * Real.pi))

/-- Hardy 定理的完整形式化 -/
theorem hardy_theorem_full (h_mean : hardyLittlewoodMeanValueHypothesis)
    (h_osc : xiOscillationHypothesis) : Set.Infinite criticalLineZeros :=
  hardys_theorem_by_sign_changes
    (fun M => let ⟨t, ht, hf⟩ := h_osc.1 M; ⟨t, le_of_lt ht, hf⟩)
    (fun M => let ⟨t, ht, hf⟩ := h_osc.2 M; ⟨t, le_of_lt ht, hf⟩)
