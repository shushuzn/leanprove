# BigO/渐近分析 API

## IsBigO.of_bound

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g
```
**说明**: 用显式常数 c 和 filter 上最终成立的 bound 证明 BigO。
**Pitfall**: 目标变成 `‖f x‖ ≤ c * ‖g x‖` 后注意双重绝对值 `|(|f x|)|`，需 `rw [abs_of_nonneg (abs_nonneg _)]` 简化。

## IsBigO.of_bound'

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g
```
**说明**: 用常数 1 的简化版本。

## IsBigO.add

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g
```
**说明**: 拆解 `(f₁ + f₂) =O g` 为两个子目标。

## IsBigO.mul

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.mul (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) : (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x
```
**Pitfall**: `f₁ f₂` 和 `g₁ g₂` 可能类型不同（`α → R` vs `α → S`），不匹配时先 `IsBigO.trans` 转换。

## IsBigO.trans

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.trans (hfg : f =O[l] g) (hgk : g =O[l] k) : f =O[l] k
```

## IsBigO.trans_le

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k
```
**说明**: 已知 f=O(g') 且 g' ≤ k 点态，则 f=O(k)。比 trans 少一个 filter 条件。

## IsBigO.comp_tendsto

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) : (f ∘ k) =O[l'] (g ∘ k)
```
**说明**: 变量替换。

## IsBigO.pow / IsBigO.sq

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.pow (h : f =O[l] g) (n : ℕ) : (fun x => f x ^ n) =O[l] fun x => g x ^ n
```
**说明**: `h.sq` 是 `h.pow 2` 的简写。

## IsBigO.mul_isLittleO

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsBigO.mul_isLittleO (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) : (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x
```
**说明**: BigO × littleO = littleO。

## IsLittleO.mul_isBigO

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsLittleO.mul_isBigO (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) : (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x
```

## IsLittleO.isBigO

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
IsLittleO.isBigO (h : f =o[l] g) : f =O[l] g
```

## isBigO_of_le

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g
```

## isBigO_of_le'

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g
```

## isBigO_const_of_tendsto

**Import**: `Mathlib.Analysis.Asymptotics.Asymptotics`
**签名**:
```lean
isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) : f'' =O[l] fun _x => c
```
**说明**: 有界函数 = O(常数)。

## 项目自定义 API

### isLittleO_const_of_tendsto_atTop

**Import**: 项目自定义引理（见 Leanprove.WienerProof）
**签名**:
```lean
isLittleO_const_of_tendsto_atTop (a : ℝ) {f : α → ℝ} (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f
```

### log_add_div_isBigO_log

**Import**: 项目自定义引理（见 Leanprove.WienerProof）
**签名**:
```lean
log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) : (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x
```
**说明**: 对于 `log(x/b)`，用 `a = 0` 然后 `simp only [add_zero]`。

### nabla_log

**Import**: 项目自定义引理（见 Leanprove.WienerProof）
**签名**:
```lean
nabla_log {b : ℝ} (hb : 0 < b) : (fun x => Real.log ((x + 1) / b) - Real.log (x / b)) =O[atTop] fun x => 1 / x
```

### log_isbigo_log_div

**Import**: 项目自定义引理（见 Leanprove.WienerProof）
**签名**:
```lean
log_isbigo_log_div {d : ℝ} (hb : 0 < d) : (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d))
```

### Asymptotics.IsBigO.add_isLittleO_right

**Import**: 项目自定义引理（见 Leanprove.WienerProof）
**签名**:
```lean
Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) : f =O[atTop] (f + g)
```

## 组合模式

### filter_upwards + of_bound 标准模式

**说明**: BigO 证明最常用模式。`apply IsBigO.of_bound C` 后 `filter_upwards` 进入点态 bound。
**Pitfall**: 绝对值简化顺序 — `Real.norm_eq_abs` → `abs_of_nonneg`（平方）→ `abs_mul` → `abs_of_pos`。
```lean
apply IsBigO.of_bound C
filter_upwards [eventually_gt_atTop N] with x hx
-- 目标: ‖f x‖ ≤ C * ‖g x‖
simp only [norm_eq_abs, one_mul]
-- 然后根据 g 的形式处理绝对值
```

### 分解 + IsBigO.add

**说明**: 将 `(f₁ + f₂) =O g` 拆为两个 BigO 再组合。
```lean
apply IsBigO.add
· exact h1  -- f₁ =O g
· exact h2  -- f₂ =O g
```

### 传递性链

**说明**: `h_fg.trans h_gk` 或 `h_fg.trans_le (fun x => ...)`（需点态 bound）。

### 乘法

```lean
exact h1.mul h2
```

### 幂次

```lean
exact h.sq   -- f² =O g²
exact h.pow 3  -- f³ =O g³
```

## 常见问题

### 双重绝对值

**问题**: `IsBigO.of_bound` 目标 `‖f x‖ ≤ c * ‖g x‖` 经 `simp only [norm_eq_abs]` 后变 `|(|f x|)| ≤ c * |(|g x|)|`。
**解决**: `rw [abs_of_nonneg (abs_nonneg _)]` 简化 `|(|a|)|` 到 `|a|`。

### rw [← Real.norm_eq_abs] 影响主目标

**问题**: `rw [← Real.norm_eq_abs]` 在 `have` 内部会改写主目标。
**解决**: 用 `rw [Real.norm_eq_abs] at this`（安全），不要用 `←`。

### linarith 看不到假设

**问题**: 在 `filter_upwards` 内部，`linarith` 可能看不到某些 `have`。
**解决**: 显式传递：`linarith [h1, h2, h3, h4]`。

### sub_le_self

**导入**: `Mathlib.Algebra.Order.Monoid`
```lean
sub_le_self {a b : ℝ} (h : 0 ≤ b) : a - b ≤ a
```
**说明**: 用于 nnabla bound 中 `u n - u (n+1) ≤ u n` 的证明。
