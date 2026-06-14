# Sorry 清单和进展

## 当前状态 (2026-06-14)

**总 sorry 数: 43**（分布在 3 个文件）

| 文件 | sorry 数 | 状态 |
|------|----------|------|
| WienerProof.lean | 29 | ❌ 编译阻塞 |
| ZetaVI/Definitions.lean | 9 | 🔄 框架已建 |
| ZetaVI/Hardy.lean | 5 | 🔄 框架已建 |

## 已证明

1. ✅ `fourierIntegral_self_add_deriv_deriv` — (1+u²)·𝓕(f) = 𝓕(f - 1/(4π²)·f'')
2. ✅ `continuous_FourierIntegral` — CS 函数 Fourier 变换连续
3. ✅ `decay_bounds_key` — 含三角不等式
4. ✅ `decay_bounds_cor` — CS 函数嵌入 W21
5. ✅ `decay_bounds_W21` — 含代数恒等式
6. ✅ `W21_integrable_fourier` — 含变量替换
7. ✅ `nnabla_mul_log_sq` — BigO 渐近分析
8. ✅ `nnabla_bound_aux` — nnabla 序列差分的 BigO bound（部分完成）

## 关键经验（见各 RAG 文件）

- BigO 渐近分析模式 → `bigo-api.md`
- nnabla 证明要点 → `nnabla-api.md`
- nnabla_bound_aux 子任务分解 → `nnabla_bound_aux-subtasks.md`
- 困难 proof 记录 → `difficult-proofs.md`
- 关键 Pitfalls → `proof-patterns.md`
- Mathlib API 用法 → `mathlib-api.md`
