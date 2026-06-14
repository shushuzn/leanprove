# 项目 Fourier 衰减定理

**Import**: `Leanprove.WienerProof`（项目自定义）

## Fourier 变换

**说明**: ℝ 上的 Fourier 变换，`𝓕 f u = ∫ v, 𝐞 (-⟪v, u⟫) • f v`，其中 `𝐞 x = exp(2πIx)`。

## W21 范数

**签名**:
```lean
noncomputable def w21norm (f : W21) : ℝ :=
  (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
```
**说明**: W21 空间（Sobolev W^{2,1}）的范数定义。

## fourierIntegral_self_add_deriv_deriv

**签名**:
```lean
theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u
```
**说明**: `(1+u²) * 𝓕(f) = 𝓕(f - 1/(4π²) * f'')`。已证明。

## decay_bounds_key

**签名**:
```lean
lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ f.w21norm * (1 + u ^ 2)⁻¹
```
**说明**: Fourier 衰减估计 `‖𝓕(f) u‖ ≤ w21norm * (1+u²)⁻¹`。已证明。

## decay_bounds_cor

**签名**:
```lean
lemma decay_bounds_cor (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2)
```
**说明**: CS 函数的 Fourier 衰减。已证明。

## decay_bounds_W21

**签名**:
```lean
lemma decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2)
```
**说明**: W21 函数的 Fourier 衰减（带常数）。**待证明**（在 WienerProof.lean 中）。
