# 证明模式和技巧

## Cast 处理模式

### 问题: `1/(4*↑π²)` vs `↑(1/(4*π²))`
```lean
-- 解决方案: 使用 push_cast + ring
have h_cast : (1 / (4 * (↑π : ℂ) ^ 2) : ℂ) = (↑(1 / (4 * π ^ 2) : ℝ) : ℂ) := by
  push_cast; ring
```

### 问题: `‖↑(1+u²)‖` vs `1+u²`
```lean
-- 解决方案: norm_real + abs_of_pos
have h_norm : ‖(↑(1 + u ^ 2 : ℝ) : ℂ)‖ = (1 + u ^ 2 : ℝ) := by
  rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

### 问题: `‖↑c * f‖` vs `c * ‖f‖`
```lean
-- 解决方案: norm_mul + norm_real + abs_of_pos
have h : ‖(↑c : ℂ) * f‖ = c * ‖f‖ := by
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
```

## 积分不等式模式

### 三角不等式积分
```lean
-- 目标: ∫‖f - c*g‖ ≤ ∫‖f‖ + c*∫‖g‖
-- 步骤:
-- 1. 点态 bound: ‖f v - c*g v‖ ≤ ‖f v‖ + c*‖g v‖
-- 2. LHS 可积: Integrable (fun v => ‖f v - c*g v‖)
-- 3. RHS 可积: Integrable (fun v => ‖f v‖ + c*‖g v‖)
-- 4. integral_mono
-- 5. RHS 拆分: integral_add + integral_mul_const
```

### 常数提取
```lean
-- 问题: 1/(4π²) * ∫‖f''‖ ≤ A/(4π)
-- 步骤:
-- 1. mul_le_mul_of_nonneg_left h_int_f'' (by positivity)
-- 2. rw [← mul_assoc]  -- 把 (1/(4π²)) * (π*A) 变成 ((1/(4π²)) * π) * A
-- 3. rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp]  -- field_simp 关闭等式
-- 4. rw [show A / (4 * π) = 1 / (4 * π) * A from by ring_nf]  -- mul_comm
-- 5. exact h
```

### 代数恒等式: `1/(4π²) * π = 1/(4π)`
```lean
-- field_simp 可以直接关闭此等式
-- 不需要 ring_nf 跟在后面
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp]
```

## 代数恒等式模式

### `field_simp` 在 `show` 内部会关闭目标
```lean
-- 问题: field_simp 在 show 内部关闭目标，导致 rw 无法使用
-- 错误: "No goals to be solved"

-- 解决方案1: 使用 mul_assoc + ring_nf 组合
rw [show (1 / (4 * π ^ 2)) * (π * A) = (1 / (4 * π ^ 2) * π) * A from by ring_nf]
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp; ring_nf]
ring_nf

-- 解决方案2: 直接使用 rw 而不是 show
rw [← mul_assoc]
rw [show (1 / (4 * π ^ 2)) * π = 1 / (4 * π) from by field_simp; ring_nf]
```

### `(4*π²)⁻¹` vs `1/(4*π²)`
```lean
-- 这两个是相等的，但 Lean 不认为它们 definitionally equal
-- 解决方案: rw [show (4 * π ^ 2)⁻¹ = 1 / (4 * π ^ 2) from by ring_nf]
```

## Fourier 变换证明模式

### 线性性
```lean
-- 𝓕(f + g) = 𝓕(f) + 𝓕(g)
F_add (hf : Integrable f) (hg : Integrable g) (x : ℝ)

-- 𝓕(c * f) = c * 𝓕(f)
F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ}
```

### 导数公式
```lean
-- 𝓕(deriv f) = (2πIu) * 𝓕(f)
fourier_deriv (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f))
```

### 二阶导数
```lean
-- deriv^[2] f = deriv (deriv f)
-- 证明: rw [← iteratedDeriv_eq_iterate (n := 2), iteratedDeriv_succ, iteratedDeriv_one]
```

## W21 相关模式

### CS → W21 嵌入
```lean
-- CS 函数是 C² 紧支集，可嵌入 W21
let f : W21 := {
  toFun := ψ
  smooth := ψ.h1
  integrable := by
    intro k hk
    interval_cases k
    · exact h_int  -- Integrable ψ
    · simp [iteratedDeriv_succ]; exact h_int'  -- Integrable (deriv ψ)
    · simp [iteratedDeriv_succ]; exact h_int''  -- Integrable (deriv (deriv ψ))
}
```

### CS 函数导数可积
```lean
-- 一阶导数
(ψ.h1.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport ψ.h2.deriv

-- 二阶导数
(ψ.h1.deriv'.continuous_deriv_one).integrable_of_hasCompactSupport ψ.h2.deriv.deriv
```

## BigO 渐近分析模式

### nnabla_bound_aux 模式
```lean
-- 目标: nnabla u n =O[atTop] v n
-- 策略:
-- 1. 证明 u n =O[atTop] v n
-- 2. 证明 |nnabla u n| ≤ u n（对于递减函数）
-- 3. 组合: h2.isBigO_trans h1
-- 关键: 展开 nnabla 定义，用 norm_eq_abs 简化绝对值
-- 类型转换: 使用 exact_mod_cast 处理 n : ℕ → (n : ℝ)
-- 绝对值处理: rw [abs_of_nonneg (sub_nonneg.mpr h_decr)] 可能失败
```

### IsBigO.of_bound + filter_upwards
```lean
-- 目标: f =O[atTop] g
-- 步骤:
-- 1. apply IsBigO.of_bound C  -- C 是常数
-- 2. filter_upwards [eventually_gt_atTop N] with x hx
-- 3. simp only [norm_eq_abs, one_mul]  -- 转换 ‖‖ 到 |...|
-- 4. 处理双重 |...|: rw [abs_of_nonneg (abs_nonneg _)]
-- 5. 处理 |a²|: rw [abs_of_nonneg (sq_nonneg _)]
-- 6. 处理 |a*b|: rw [abs_mul]
-- 7. 处理 |a| when a > 0: rw [abs_of_pos h]
```

### log 恒等式
```lean
-- log(x/b) = log x - log b
Real.log_div hx' hb' : Real.log (x / b) = Real.log x - Real.log b

-- log(x/(x-1)) = log x - log(x-1)
Real.log_div hx' hx1' : Real.log (x / (x - 1)) = Real.log x - Real.log (x - 1)

-- log(x/b) = O(log x)
log_add_div_isBigO_log 0 hb : (fun x => Real.log (x + 0 / b)) =O[atTop] Real.log
-- 需要 simp only [add_zero] 来简化

-- a²-b² = (a-b)(a+b)
-- 用 ring_nf 证明
```

### BigO 组合
```lean
-- IsBigO.add: f₁ =O g → f₂ =O g → (f₁ + f₂) =O g
-- IsBigO.mul: f₁ =O g₁ → f₂ =O g₂ → (f₁ * f₂) =O (g₁ * g₂)
-- IsBigO.pow: f =O g → f^n =O g^n
-- isLittleO_const_of_tendsto_atTop: const =o g when g → ∞
```

### rw 在 filter_upwards 上下文中的行为
```lean
-- 问题: rw [← Real.norm_eq_abs] 在 have 内部会影响主目标
-- 解决方案:
--   1. 用 convert_to + congr_arg₂ 代替 rw
--   2. 用 rw [Real.norm_eq_abs] at this (安全，不影响主目标)
--   3. linarith 需要显式传递假设: linarith [h1, h2, h3, h4]

-- convert_to 用法:
convert_to new_goal using 1
· exact congr_arg₂ (fun a b => |a + b|) eq1 eq2

-- norm_add_le 转换:
have h_raw := norm_add_le a b
rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
-- h_raw : |a + b| ≤ |a| + |b|
```

---

## 关键 Pitfalls（来自 skill）

### ⚠️ field_simp 在 show/have 内部关闭目标
```lean
-- ❌ 错误: field_simp 关闭目标后 ring_nf 报 "No goals to be solved"
rw [show a = b from by field_simp; ring_nf]  -- ring_nf 多余

-- ✅ 正确: field_simp 单独关闭等式
rw [show a = b from by field_simp]

-- ✅ 正确: 需要 field_simp + ring_nf 时分步写
rw [show a = b from by field_simp]
rw [show b = c from by ring_nf]
```

### ⚠️ (a*b)*c = d 的拆解模式
```lean
-- 目标: (1/(4π²)) * (π * A) = A/(4π)
-- ❌ 错误: 直接 field_simp; ring_nf 可能在 show 内部行为不一致
-- ✅ 正确: 拆解为 mul_assoc + 简化 + ring_nf
rw [← mul_assoc]  -- 变成 ((1/(4π²)) * π) * A
rw [show (1/(4π²)) * π = 1/(4π) from by field_simp]
rw [show A/(4π) = 1/(4π) * A from by ring_nf]
exact h
```

### ⚠️ rw [← Real.norm_eq_abs] 在 have 内部影响主目标
```lean
-- 问题: rw [← Real.norm_eq_abs] 在 have 内部会改写主目标中的 |...| 为 ‖...‖
-- 这导致后续 linarith 看到 ⊢ False
-- 根因: rw 在某些上下文（filter_upwards + have）中会意外影响主目标
-- 解决方案:
--   1. 用 convert_to + congr_arg₂ 代替 rw 来替换等式
--   2. 用 rw [Real.norm_eq_abs] at this 而不是 rw [← Real.norm_eq_abs]
--   3. linarith 需要显式传递假设: linarith [h1, h2, h3, h4]
-- 关键: rw [← X] 比 rw [X] 更容易出问题
```

### ⚠️ IsBigO.of_bound 目标中 rwc 失败时用 nlinarith 不行
```lean
-- 问题: nlinarith 内部用 linarith，无法处理 Real.log 等非线性函数
-- 当 h_log_bound 包含 Real.log 时，nlinarith 仍然失败
-- 解决方案: 用 calc 分步 + linarith 组合
```

### ⚠️ BigO.of_bound 需要 eventually_gt_atTop 足够大
```lean
-- 问题: IsBigO.of_bound C 的目标是 ‖f x‖ ≤ C * ‖g x‖
-- 当 g(x) = log²x 且 bound 涉及 log x，需要 log x > 1
-- 即 x > e ≈ 2.718
-- 解决方案: 用 eventually_gt_atTop 3 或更大
-- 证明 log x > 1:
have h_log_gt1 : (1 : ℝ) < Real.log x := by
  have h_exp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_exp_lt_x : Real.exp 1 < x := lt_trans Real.exp_one_lt_three hx
  rw [← Real.log_exp 1]
  exact Real.log_lt_log h_exp_pos h_exp_lt_x
```

### ⚠️ 4|log x| + 4|log b| ≤ C * log²x 需要 log x > 1
```lean
-- 当 x > 3 > e，log x > 1
-- 4 * log x ≤ 4 * log x * log x（因为 1 ≤ log x）
-- 4 * |log b| ≤ 4 * |log b| * log x * log x（因为 1 ≤ log x）
have h4 : (4 : ℝ) * Real.log x ≤ 4 * Real.log x * Real.log x := by
  have : (1 : ℝ) ≤ Real.log x := le_of_lt h_log_gt1
  nlinarith [sq_nonneg (Real.log x), this]
have h5 : (4 : ℝ) * |Real.log b| ≤ 4 * |Real.log b| * Real.log x * Real.log x := by
  have : (1 : ℝ) ≤ Real.log x := le_of_lt h_log_gt1
  nlinarith [sq_nonneg (Real.log x), this, abs_nonneg (Real.log b)]
-- 组合用 linarith（不用 nlinarith）
```

### ⚠️ Real.log_le_sub_one_of_pos 产生需要 linarith 处理的非标准形式
```lean
-- Real.log_le_sub_one_of_pos: log(x) ≤ x - 1
-- 应用到 x/(x-1) 后: log(x/(x-1)) ≤ (x - (x-1)) / (x-1) = 1/(x-1)
-- 但 linarith 看到的是 1/(x-1) 而不是 2/(x-1)
-- 解决方案: 用 rw [show (x - (x-1)) / (x-1) = 1/(x-1) from by ring] 简化
have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < x) hx1)
rw [div_sub_one hx1'] at h
rw [show (x - (x - 1)) / (x - 1) = (1 : ℝ) / (x - 1) from by ring] at h
have h2 : (1 : ℝ) / (x - 1) ≤ 2 / (x - 1) := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hx1)
linarith [h, h2]
```

### ⚠️ Real.exp_one_lt_three 需要 import
```lean
-- Real.exp_one_lt_three : exp 1 < 3（在 Real namespace 中）
-- 需要 import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.ExponentialBounds
-- 然后用 Real.exp_one_lt_three
```

### ⚠️ div_pos 需要显式类型
```lean
-- div_pos (by linarith) hx1 在 have 内部会失败
-- 因为 linarith 推断类型时缺少上下文
-- 解决方案: 显式提供类型
div_pos (by linarith : 0 < x) hx1
```

### ⚠️ linarith 需要显式传递假设
```lean
-- 问题: 在复杂的 filter_upwards + have 上下文中，linarith 可能看不到某些假设
-- 即使假设在 context 中，linarith 也可能报 "failed to find a contradiction"

-- ❌ 失败:
linarith

-- ✅ 成功:
linarith [h1_raw, h2, h3, h4]

-- 原因: 在 filter_upwards 内部，某些 have 引入的假设可能被 linarith 忽略
-- 解决方案: 总是显式传递关键假设
```

### ⚠️ convert_to + congr_arg₂ 替换等式
```lean
-- 当 rw 在 filter_upwards 内部行为异常时，用 convert_to 代替
-- convert_to new_goal using 1 会生成一个 side goal: old_goal = new_goal

-- 用法:
have h_sum : |f x + g x| ≤ C := by
  convert_to |f' x + g' x| ≤ C using 1
  · -- 证明 f x + g x = f' x + g' x
    exact congr_arg₂ (fun a b => |a + b|) (Real.log_div hx' hb') (Real.log_div ... ...)
  -- 继续证明 |f' x + g' x| ≤ C
  ...

-- 注意: congr_arg₂ 的参数顺序很重要
-- congr_arg₂ (fun a b => |a + b|) h_eq1 h_eq2
-- h_eq1 : f x = f' x, h_eq2 : g x = g' x
```

### ⚠️ IsBigO.of_bound 产生双重绝对值
```lean
-- 问题: IsBigO.of_bound 的目标是 ‖f x‖ ≤ c * ‖g x‖
-- simp only [norm_eq_abs] 后变成 |(|f x|)| ≤ c * |(|g x|)|
-- 需要 rw [abs_of_nonneg (abs_nonneg _)] 来简化 |(|a|)| 到 |a|
-- 对于 |g x| = |log x²| = |(log x)²|，用 abs_of_nonneg (sq_nonneg _)
```

### ⚠️ nnabla 序列差分的 BigO 证明
```lean
-- 目标: nnabla (fun n => 1/(n*((2π)²+log(n/x)²))) =O[atTop] (fun n => 1/(n²*log²n))
-- 关键观察:
--   1. nnabla u n = u n - u (n+1)
--   2. u 递减时 nnabla u n ≥ 0，所以 |nnabla u n| = nnabla u n
--   3. nnabla u n = u n - u (n+1) ≤ u n
-- 策略: IsBigO.of_bound 1 + filter_upwards
-- Pitfall: le_div_iff₀' 类型不匹配需要 exact_mod_cast
-- 详见 references/nnabla-bigo-patterns.md
```

### ⚠️ Integrable.smul 类型推断卡住
```lean
-- ❌ 错误: Lean 无法推断标量类型
exact (W21.hf'' f).smul _

-- ✅ 正确: 显式提供标量类型
exact (W21.hf'' f).smul (↑c : ℂ)
```

### ⚠️ integral_mul_const vs integral_const_mul
```lean
-- integral_mul_const: ∫ (f * c) = (∫ f) * c
-- integral_const_mul: ∫ (c * f) = c * ∫ f  (通过 mul_comm 转换)
-- 实际用法:
rw [show (fun v => c * ‖f v‖) = (fun v => ‖f v‖ * c) from by ext v; rw [mul_comm]]
rw [integral_mul_const]; rw [mul_comm]
```

### ⚠️ log(1+t) ≤ t 模式 (用于 BigO bound)
```lean
-- |log(x/(x-1))| ≤ 2/(x-1) 当 x > 2
-- 关键步骤:
-- 1. 证明 1 < x/(x-1): rw [lt_div_iff₀' hx1]; linarith
-- 2. |log(x/(x-1))| = log(x/(x-1)): rw [abs_of_pos (Real.log_pos h1)]
-- 3. x/(x-1) - 1 = 1/(x-1): rw [div_sub_one hx1.ne']; ring_nf
-- 4. log(x/(x-1)) ≤ x/(x-1) - 1: Real.log_le_sub_one_of_pos h_div_pos
-- 5. 1/(x-1) ≤ 2/(x-1): div_le_div_of_nonneg_right (by linarith) (le_of_lt hx1)
-- 6. linarith 组合

-- 常用 API:
-- lt_div_iff₀' : a < b / c ↔ a * c < b (当 0 < c)
-- div_sub_one : a / b - 1 = (a - b) / b (当 b ≠ 0)
-- Real.log_le_sub_one_of_pos : 0 < x → log x ≤ x - 1
-- div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a / c ≤ b / c
-- abs_sub : |a - b| ≤ |a| + |b|  (注意: 不是 abs_sub_le，后者有不同签名)
-- norm_add_le : ‖a + b‖ ≤ ‖a‖ + ‖b‖  (产生 ‖‖ 不是 |...|，需要 rw [Real.norm_eq_abs] at this)
-- mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d
-- mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b
-- one_lt_div : 0 < c → (1 < a / c ↔ c < a)  (用于证明 1 < x/(x-1))
```

### ⚠️ |a + b| ≤ |a| + |b| 模式 (用 norm_add_le)
```lean
-- 对于实数: |a + b| ≤ |a| + |b|
-- 方法1: exact abs_add a b  (如果 abs_add 存在，Lean 4 中可能不存在)
-- 方法2: 用 norm_add_le + rw [Real.norm_eq_abs] at this（安全）
have h : |a + b| ≤ |a| + |b| := by
  have h_raw := norm_add_le a b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h_raw
  exact h_raw

-- ❌ 不安全（在 have 内部会影响主目标）:
-- rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]; exact norm_add_le _ _

-- |a - b| ≤ |a| + |b| (用 abs_sub)
have h : |a - b| ≤ |a| + |b| := abs_sub _ _
```

### ⚠️ Ne.symm (ne_of_lt) 模式
```lean
-- 将 0 < b 转换为 b ≠ 0 (用于 Real.log_div 等需要 b ≠ 0 的引理)
rw [Real.log_div (by linarith) (Ne.symm (ne_of_lt hb))]
```
