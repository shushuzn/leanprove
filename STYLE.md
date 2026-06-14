# Lean 4 代码风格规范

本项目遵循 [mathlib4 代码风格](https://github.com/leanprover-community/mathlib4) 的惯例。

## 1. 文件结构

每个 `.lean` 文件按以下顺序排列：

```lean
/-
Copyright (c) 2026 <作者名>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <作者名>
-/

import Mathlib.X.Y.Z              -- 标准库导入
import Leanprove.OtherModule      -- 项目内部导入

open X Y                           -- open 声明
open scoped Z                      -- scoped open

/-! # 模块标题

模块描述（可选）。

## Main definitions/Results

* `def_name` — 一句话说明
* `lemma_name` — 一句话说明
-/

noncomputable section               -- 如果有 noncomputable

/-- 简短描述 -/
def foo : ℕ := 42

/-- 多行描述：如果需要更多说明，
    写在第二行。 -/
lemma bar_eq (x : ℕ) : bar x = x := by
  rfl
```

## 2. 命名规范

| 项 | 规则 | 示例 |
|---|------|------|
| 定理/引理 | `snake_case` | `zeta_bound_at_two` |
| 定义 | `camelCase` | `completedZeta` |
| 类型 | `CamelCase` | `W21` |
| 文件/模块 | `PascalCase` | `ZetaVI/Definitions` |

## 3. Docstring 格式

```lean
/-- 一行能写完的简短描述 -/
def shortDoc (x : ℕ) : ℕ := x

/-- 多行描述：注意缩进对齐

    可以包含空行，以及引用链接。 -/
lemma longerDoc (x y : ℕ) (h : x ≤ y) : x ≤ y := h
```

**规则:**
- 所有 `def`、`lemma`、`theorem` 必须有 `/- ... -/` docstring。
- 一行能写完的用 `/- 描述 -/` 在一行内。
- 多行时第二行缩进与第一行文本对齐。
- 文档描述"做什么"，不写"怎么实现"（实现在代码里）。

## 4. Import 规范

- 标准库导入放在项目导入之前。
- 只导入你实际需要的模块。
- 不使用 `public import` 除非明确需要 re-export。

## 5. 证明格式

```lean
-- ✅ 简短的证明用 :=
lemma trivial_example : 1 + 1 = 2 := by norm_num

-- ✅ 较长的证明用 calc
lemma calc_example (x y : ℂ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

-- ✅ 需要额外步骤的用 by block
lemma block_example (x : ℝ) (hx : 0 < x) : 0 < x^2 := by
  exact pow_pos hx 2
```

**规则:**
- 证明不超过 30 行。超过的拆分为子引理。
- 使用 `calc` 表示等式链。
- 每个 `have` 一个原子步骤。
- 不用 `?_`（elaborator hole），用 `sorry`。

## 6. 文档注释（`/-!`）

模块级文档使用 `/-! ... -/`，放在 imports 之后、代码之前：

```lean
/-! # 模块名

## Main definitions

* `DefName` — 描述
```

## 7. 参考

- [mathlib4 贡献指南](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md)
- [mathlib4 代码风格](https://leanprover-community.github.io/contribute/style.html)
