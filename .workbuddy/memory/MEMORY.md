# leanprove Project Memory

## 编译环境
- Lean 4.31.0-rc2, Windows LLVM 后端 bug 导致 lake build 崩溃
- mathlib 构建缓存已恢复（25,564 .ltar 解压完成）

## 文件状态
- **Sobolev.lean** ✅ 已提供 CS n E、W1 n E、W21 定义
- **Tauberian.lean** ⚠️ 3个sorry
  - `WienerIkeharaInterval` (L119): 需要从源文件移植区间版公式
  - `WienerIkeharaInterval_discrete'` (L128): 离散区间版
  - `WienerIkeharaTheorem` (L161): 核心 Wiener-Ikehara 定理
  - ✅ G_weakPNT, G_continuous, WeakPNT 已定义但依赖 WienerIkeharaTheorem
- **VonMangoldt.lean** ✅ 全部完成，0个sorry
- **WienerProof.lean** 🚧 已移植傅里叶变换核心引理和 W21 衰减估计
  - 已完成: fourierIntegral_self_add_deriv_deriv, decay_bounds_key, decay_bounds_cor
  - 待移植 ~1500行: limiting_fourier_* → limiting_cor → wiener_ikehara_smooth → WienerIkeharaInterval → WienerIkeharaTheorem

## 项目目标
- ✅ VonMangoldt: primePower_contribution_bounded + psi_integral_sub_log_isBigO
- 🚧 Tauberian: WienerIkeharaTheorem (3个sorry)
- 🔜 通过 WienerIkeharaTheorem 证明 WeakPNT
