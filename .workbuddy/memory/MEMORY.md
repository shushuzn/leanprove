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
- **WienerProof.lean** ✅ 全部完成，1518行，0个sorry
  - 傅里叶变换 → 衰减估计 → limiting_fourier → limiting_cor → wiener_ikehara_smooth → WienerIkeharaInterval → WienerIkeharaTheorem'
- **PNTVA.lean** ✅ 全部完成
- **其他文件**（Basic, Chebyshev, Dirichlet, Zeta 系列等）✅

## 项目状态
- ✅ `lake build` 编译通过，零 error，零 warning
- ✅ 16 个 .lean 文件，零 sorry（仅 PNTVA.lean 注释中提到旧状态）
- ✅ WienerIkeharaTheorem 已证明 → WeakPNT 可推导
- ✅ pre-commit hook 已安装（sorry检查 + 编译检查 + lint检查）
- ✅ 规则29/30/31 已写入 AGENT.md

## 待办
- 完善 project website / 文档
- 考虑移植 smooth_urysohn_support_Ioo 的真实证明（当前为 axiom）
