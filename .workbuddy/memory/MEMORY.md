# leanprove Project Memory

## 编译环境
- Lean 4.31.0-rc2, Windows LLVM 后端 bug 导致 lake build 崩溃
- mathlib 构建缓存已恢复（25,564 .ltar 解压完成）

## 文件状态
- **Sobolev.lean** ✅ 基础函数空间定义
- **Tauberian.lean** ⚠️ 3个sorry（WienerIkeharaInterval, WienerIkeharaInterval_discrete', WienerIkeharaTheorem）
- **VonMangoldt.lean** ✅ 全部完成，0个sorry
- **WienerProof.lean** 🚧 已移植大部分证明（~1370行）
  - ✅ Fourier 变换核心性质: F_sub, F_mul, fourierIntegral_self_add_deriv_deriv
  - ✅ W21 衰减估计: decay_bounds_key, decay_bounds_cor
  - ✅ 级数分析: dirichlet_test', summation_by_parts, summable_inv_mul_log_sq
  - ✅ 渐近估计: nabla_log, nnabla_mul_log_sq, nnabla_bound
  - ✅ limiting_fourier_lim1/2/3, limiting_fourier, limiting_cor
  - ✅ first_fourier, second_fourier, limiting_fourier_aux
  - ✅ fourier_surjection_on_schwartz, wiener_ikehara_smooth
  - ✅ interval_approx_sup/inf (依赖 smooth_urysohn_support_Ioo 使用 axiom)
  - ✅ WI_summable, WI_tendsto_aux 等辅助引理
  - ❌ residue_nonneg (剩余)
  - ❌ WienerIkeharaInterval 完整证明
  - ❌ WienerIkeharaTheorem' 完整证明

## 项目目标
- ✅ VonMangoldt: primePower_contribution_bounded + psi_integral_sub_log_isBigO
- 🚧 WienerProof: 还需填充 residue_nonneg + WienerIkeharaInterval 证明 (~200行)
- 🔜 通过 WienerIkeharaTheorem 证明 WeakPNT
