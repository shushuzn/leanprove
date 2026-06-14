# Mathlib BigO/渐近分析 API 完整参考

## 核心 API

### IsBigO.of_bound
```lean
-- 用常数 bound 证明 BigO
IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g
```

### IsBigO.of_bound'
```lean
-- 用 1 作为常数
IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g
```

### IsBigO.add
```lean
-- BigO 加法: f₁ =O g → f₂ =O g → (f₁ + f₂) =O g
IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g
```

### IsBigO.mul
```lean
-- BigO 乘法: f₁ =O g₁ → f₂ =O g₂ → (f₁ * f₂) =O (g₁ * g₂)
IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x
```

### IsBigO.trans
```lean
-- 传递性: f =O g → g =O k → f =O k
IsBigO.trans (hfg : f =O[l] g) (hgk : g =O[l] k) : f =O[l] k
```

### IsBigO.trans_le
```lean
-- 传递性 + 点态 bound: f =O g → (∀ x, ‖g x‖ ≤ ‖k x‖) → f =O k
IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k
```

### IsBigO.comp_tendsto
```lean
-- 复合: f =O g → Tendsto k l' l → (f ∘ k) =O (g ∘ k)
IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k)
```

### IsBigO.pow
```lean
-- 幂次: f =O g → f^n =O g^n
IsBigO.pow [NormOneClass S] (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n
```

### IsBigO.mul_isLittleO
```lean
-- BigO * LittleO = LittleO
IsBigO.mul_isLittleO (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x
```

### IsLittleO.mul_isBigO
```lean
-- LittleO * BigO = LittleO
IsLittleO.mul_isBigO (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x
```

### IsLittleO.isBigO
```lean
-- LittleO ⊂ BigO
IsLittleO.isBigO (h : f =o[l] g) : f =O[l] g
```

### isBigO_of_le
```lean
-- 点态 bound → BigO
isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g
```

### isBigO_of_le'
```lean
-- 常数 * 点态 bound → BigO
isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g
```

### isBigO_const_of_tendsto
```lean
-- 有界函数 =O 常数
isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun _x => c
```

## 项目自定义 API

### isLittleO_const_of_tendsto_atTop
```lean
-- 常数 =o f 当 f → ∞
isLittleO_const_of_tendsto_atTop (a : ℝ) {f : α → ℝ} (hf : Tendsto f atTop atTop) :
    (fun _ => a) =o[atTop] f
```

### log_add_div_isBigO_log
```lean
-- log(x + a / b) = O(log x)
log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x
-- 对于 log(x/b): 用 a = 0, 然后 simp only [add_zero]
```

### nabla_log
```lean
-- log((x+1)/b) - log(x/b) = O(1/x)
nabla_log {b : ℝ} (hb : 0 < b) :
    (fun x => Real.log ((x + 1) / b) - Real.log (x / b)) =O[atTop] fun x => 1 / x
```

### log_isbigo_log_div
```lean
-- log(n) = O(log(n/d))
log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d))
```

### Asymptotics.IsBigO.add_isLittleO_right
```lean
-- f =O (f + g) 当 g =o f
Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g)
```

## 组合模式

### 模式1: 分解 + 组合
```lean
-- 目标: (f₁ + f₂) =O g
-- 分解为 f₁ =O g 和 f₂ =O g，然后用 IsBigO.add
apply IsBigO.add
· exact h1
· exact h2
```

### 模式2: 乘法组合
```lean
-- 目标: (f₁ * f₂) =O (g₁ * g₂)
-- 分别证明 f₁ =O g₁ 和 f₂ =O g₂，然后用 IsBigO.mul
exact h1.mul h2
```

### 模式3: 传递性
```lean
-- 目标: f =O k
-- 先证明 f =O g，再证明 g =O k
exact h1.trans h2
-- 或者用 trans_le:
exact h1.trans_le (fun x => by linarith)
```

### 模式4: 复合
```lean
-- 目标: (f ∘ k) =O (g ∘ k)
-- 先证明 f =O g，再用 comp_tendsto
exact h.comp_tendsto tendsto_id
```

### 模式5: 幂次
```lean
-- 目标: f² =O g²
-- 先证明 f =O g，再用 .sq 或 .pow 2
exact h.sq  -- 或 h.pow 2
```

### 模式6: 常数 =o f
```lean
-- 目标: (fun _ => a) =o f
-- 当 f → ∞
exact isLittleO_const_of_tendsto_atTop a hf
```

### 模式7: BigO + LittleO = BigO
```lean
-- 目标: (f₁ + f₂) =O g
-- 当 f₁ =O g 且 f₂ =o g
exact h1.add_isLittleO h2
```

### 模式8: filter_upwards + of_bound
```lean
-- 目标: f =O[atTop] g
apply IsBigO.of_bound C
filter_upwards [eventually_gt_atTop N] with x hx
-- 现在目标: ‖f x‖ ≤ C * ‖g x‖
-- 处理绝对值:
rw [Real.norm_eq_abs, Real.norm_eq_abs]
rw [abs_of_nonneg (sq_nonneg _)]  -- |a²| = a²
rw [abs_mul]  -- |a*b| = |a|*|b|
rw [abs_of_pos h]  -- |a| = a when a > 0
```

## 常见问题

### 问题1: IsBigO.of_bound 产生双重绝对值
```lean
-- simp only [norm_eq_abs] 后: |(|f x|)| ≤ c * |(|g x|)|
-- 解决: rw [abs_of_nonneg (abs_nonneg _)] 简化 |(|a|)| 到 |a|
```

### 问题2: rw [← Real.norm_eq_abs] 在 have 内部影响主目标
```lean
-- 解决: 用 rw [Real.norm_eq_abs] at this (安全)
have h_raw := norm_add_le a b
rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
```

### 问题3: linarith 看不到某些假设
```lean
-- 解决: 显式传递假设
linarith [h1, h2, h3, h4]
```

### 问题4: IsBigO.mul 的类型不匹配
```lean
-- IsBigO.mul 需要 f₁ : α → R, f₂ : α → R, g₁ : α → S, g₂ : α → S
-- 如果类型不匹配，需要用 IsBigO.trans 先转换
```
