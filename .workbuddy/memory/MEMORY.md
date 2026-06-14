# leanprove Project Memory

## 编译环境
- Lean 4.31.0-rc2
- mathlib 构建缓存已恢复
- `lake build` 编译失败（WienerProof.lean 阻塞）

## 项目概览
- 22 个 .lean 文件（不含 .lake 和 tmp/），总计约 6700 行
- **43 个实际 sorry**（分布在 3 个文件），**0 个 axiom**
- 0 个 `admit` / `#exit`

## 文件状态

### ✅ 已完成的文件（0 sorry）
| 文件 | 行数 | 说明 |
|------|------|------|
| VonMangoldt.lean | 1313 | 含 2 个 lint 警告（无影响） |
| Basic.lean | 677 | 基础定义与引理 |
| Dirichlet.lean | 527 | Dirichlet 卷积 |
| PNTVA.lean | 494 | 素数定理陈述，0 real sorry |
| Tauberian.lean | 466 | Wiener-Ikehara 定理完全证明 |
| Chebyshev.lean | 308 | Chebyshev 估计 |
| ZetaVI/Asymptotics.lean | 219 | Hardy 定理渐近分析 |
| ZetaIVB.lean | 184 | |
| PrimeCounting.lean | 174 | |
| Sobolev.lean | 113 | 基础函数空间定义 |
| ZetaIVD.lean | 96 | |
| ZetaIVE.lean | 107 | |
| Tests.lean | 89 | |
| Bertrand.lean | 86 | |
| ApiCheck.lean | 39 | |
| PrimeReciprocals.lean | 35 | |
| ZetaVI.lean | 25 | 主入口（仅 import + 框架） |
| MathlibTest.lean | 5 | |
| Leanprove.lean | 15 | 主索引文件 |

### ⚠️ 有待完成的文件
| 文件 | 行数 | sorry 数 | 状态 |
|------|------|----------|------|
| **WienerProof.lean** | 1221 | **29** | ❌ 编译错误，全文件阻塞 |
| **ZetaVI/Definitions.lean** | 233 | **9** | 🔄 框架已建，证明待补 |
| **ZetaVI/Hardy.lean** | 253 | **5** | 🔄 Hardy 定理核心证明 |

## 当前问题

### WienerProof.lean（29 sorries，阻塞编译）
**根本原因：** 文件从未成功编译，预存错误贯穿全文。已标记为 sorry 的引理构成级联依赖链：
```
傅里叶变换 → 衰减估计 → limiting_fourier → limiting_cor → wiener_ikehara_smooth → WienerIkeharaInterval → WienerIkeharaTheorem'
```

**缺失的 Mathlib API（需在 v4.31.0-rc2 中查找新名称）：**
- `limiting_fourier_lim2` → 已重命名或移除
- `mem_nhdsWithin_Icc_iff_Ioo` → 已重命名
- `SmoothTransition`（原 `Real.smoothTransition`）→ 其他名称
- `BoundedAtFilter.add_const` / `comp_add` → 已移除
- `isOpen_closure.symm` → 已移除
- `Homeomorph.exp` → 已移除
- `toSchwartz_apply` → 未定义

### ZetaVI 模块（14 sorries）
- **Definitions.lean（9 sorries）**: Zeta 函数关键性质的证明缺漏
- **Hardy.lean（5 sorries）**: 核心 Hardy 定理证明中需完善；注释标明需要 riemannXi 的连续性和解析性、非零解析函数零点孤立性

## 专家创建
- 2026-06-14：基于本项目创建了 **lean-formal-prover**（Lean 形式化证明专家）
  - Agent 型，行业分类 02-Engineering（技术工程）
  - 注册于 `~/.workbuddy/plugins/marketplaces/my-experts/plugins/lean-formal-prover/`

## 待办（按优先级）
1. **修复 WienerProof.lean 编译错误**（29 sorries，阻塞全局编译）
2. **完善 ZetaVI/Hardy.lean 证明**（5 sorries）
3. **完善 ZetaVI/Definitions.lean 证明**（9 sorries）
4. 清理 VonMangoldt.lean 的 2 个 lint 警告

## 数据库信息
- 项目ID: `8a06a625-54c2-4a07-bd2a-5b56a03ed52a`
- mimocode.db 位于 `C:\Users\35234\.local\share\mimocode\mimocode.db`
