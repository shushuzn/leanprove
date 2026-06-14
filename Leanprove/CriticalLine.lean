/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

/-! # CriticalLine

Phase VI: Riemann Xi function and Hardy's theorem.

ξ(s) = s(s-1)π^{-s/2}Γ(s/2)ζ(s)

本文件是阶段 VI 的聚合导入模块，包含三个子模块：
- Definitions.lean — 基础定义（completedZeta, riemannXi, criticalStrip, N(T)）
- Hardy.lean — Hardy 定理框架（临界线零点、IVT、无限变号归约）
- Asymptotics.lean — 渐近分析核心（Gamma 渐近、均值积分归约）

完整的 Hardy 定理证明链：
1. ξ(s) 的基本性质（Definitions）
2. 临界线参数化与实值限制（Hardy）
3. IVT + 无限变号 → 无限零点（Hardy）
4. 均值积分 + Gamma 渐近 → 振荡性（Asymptotics）
5. 振荡性 → 无限零点（Hardy） -/

import Leanprove.CriticalLine.Definitions
import Leanprove.CriticalLine.Hardy
import Leanprove.CriticalLine.Asymptotics

-- 导出所有子模块的内容
export Leanprove.CriticalLine.Definitions
export Leanprove.CriticalLine.Hardy
export Leanprove.CriticalLine.Asymptotics