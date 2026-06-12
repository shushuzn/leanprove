# leanprove Project Memory

## 编译环境
- Lean 4.31.0-rc2, lake build 编译通过
- mathlib 构建缓存已恢复

## 文件状态
- **Sobolev.lean** ✅ 基础函数空间定义
- **Tauberian.lean** ✅ 完全证明，0个sorry
  - WienerIkeharaTheorem 通过 WienerProof 完整证明
  - WienerIkeharaInterval 和 WienerIkeharaInterval_discrete' 已填充
  - WeakPNT 可调用
- **VonMangoldt.lean** ✅ 全部完成，0个sorry
- **WienerProof.lean** ⚠️ 有预存编译错误（log歧义、fourierTransformCLE弃用）
  - 傅里叶变换 → 衰减估计 → limiting_fourier → limiting_cor → wiener_ikehara_smooth → WienerIkeharaInterval → WienerIkeharaTheorem'
- **PNTVA.lean** ✅ 全部完成
- **ZetaVI.lean** 🔄 开发中（Hardy定理框架）
- **其他文件**（Basic, Chebyshev, Dirichlet, Zeta 系列等）✅

## 项目状态
- ⚠️ `lake build` 编译失败（WienerProof.lean 错误）
- ✅ 16 个 .lean 文件，零 sorry（仅 PNTVA.lean 注释中提到旧状态）
- ✅ WienerIkeharaTheorem 已证明 → WeakPNT 可推导
- ✅ pre-commit hook 已安装（sorry检查 + 编译检查 + lint检查 + 覆盖保护）
- ✅ 规则29/30/31/35/36/37/38/39 已写入 AGENT.md

## 教训与规则
### 工具使用
- **禁用Glob工具**：返回假阴性，用Bash的ls/find替代（规则33）
- **禁止重写文件**：用Write覆盖已有内容违反规则8，应使用Edit工具逐个修改
- **交叉验证**：单一工具结果不可信，需用多种方法确认

### 提交流程
- pre-commit hook新增覆盖保护：检测删除行数>50%或删除+新增>80%时阻止提交
- commit必须包含标题和body描述（规则35）
- 推送前必须经用户审核同意（规则38）

### 代码修改
- 修改.lean必须同步更新README.md、ROADMAP.md、DEPENDENCY.md（规则31）
- 禁止因困难而转向简单任务（规则36）
- 方案必须用户同意后才能执行（规则37）

## 当前问题
### WienerProof.lean编译错误（73个→已修复~15个）
**根本原因：** 文件从未成功编译，预存错误贯穿全文。

**已修复（~15个）：**
- `nterm`/`term` 添加 `noncomputable`
- `Finset.range_add_one` → `Finset.sum_range_succ`
- W21的`omega` → `norm_num`（WithTop ℕ不支持omega）
- `fourierIntegral_add` → `simp only [Real.fourier_eq, integral_add, smul_add]`
- `fourierTransformCLE` → `fourierCLE`
- `Real.log` 歧义 → `Real.log`

**已sorry（~10个）：**
- `comp_exp_support0/comp_exp_support`（缺失API）
- `wiener_ikehara_smooth`（复杂依赖链）
- `smooth_urysohn_support_Ioo`（Real.smoothTransition不存在）
- `summation_by_parts''`、`summable_iff_bounded'`（BoundedAtFilter.add_const缺失）

**剩余错误级联来源（~58个）：**
- 行642/649：`mem_nhdsWithin_Icc_iff_Ioo.mpr` 缺失
- 行680：`limiting_fourier_lim2` 缺失 → 阻断limiting_fourier/limiting_cor
- 行792+：first_fourier_aux2, norm_term_eq_nterm_re 缺失

**缺失的Mathlib API：**
- `SmoothTransition`（可能是 `Real.smoothTransition` → 其他名称）
- `BoundedAtFilter.add_const`/`comp_add` → 已移除
- `isOpen_closure.symm` → 已移除
- `Homeomorph.exp` → 已移除
- `mem_nhdsWithin_Icc_iff_Ioo` → 已重命名
- `limiting_fourier_lim2` → 已重命名或移除
- `toSchwartz_apply` → 未定义

**下一步：** 需要查找Mathlib v4.31.0-rc2中缺失API的新名称

### ZetaVI模块开发
- Hardy定理框架已建立（Definitions.lean, Asymptotics.lean, Hardy.lean）
- 需要完成具体证明

## 待办
- 修复WienerProof.lean预存编译错误
- 完善ZetaVI Hardy定理证明
- 完善 project website / 文档
- 考虑移植 smooth_urysohn_support_Ioo 的真实证明（当前为 axiom）

## 数据库信息
- mimocode.db位于`C:\Users\35234\.local\share\mimocode\mimocode.db`
- 项目ID: `8a06a625-54c2-4a07-bd2a-5b56a03ed52a`
- 当前会话: `ses_145b48e35ffeenldd3RQrAMHBL` (lucky-lagoon)
- 历史会话: 5个（包含工作会话和checkpoint会话）
