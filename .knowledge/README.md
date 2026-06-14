# Leanprove RAG 知识库

本目录存储项目证明过程中积累的知识，用于提高后续证明效率。

## 文件结构

- `mathlib-api.md` — Mathlib API 用法记录（含积分、Fourier、ContDiff、BigO 等）
- `proof-patterns.md` — 证明模式和技巧（含 Cast、积分不等式、Fourier、W21、关键 Pitfalls）
- `bigo-api.md` — BigO/渐近分析 API 完整参考
- `nnabla-api.md` — nnabla/nabla 序列差分 API
- `fourier-transform.md` — Fourier 变换相关 API
- `project-structure.md` — 项目文件和依赖关系
- `sorry-inventory.md` — 当前 sorry 清单和进展
- `difficult-proofs.md` — 困难 proof 记录和分析
- `F_add-subtasks.md` — F_add 子任务分解
- `nnabla_bound_aux-subtasks.md` — nnabla_bound_aux 子任务分解

## 使用规则

1. **证明前**: 查阅相关知识文件（尤其是 `mathlib-api.md`、`proof-patterns.md` 和 `bigo-api.md`）
2. **证明中**: 遇到困难查阅 `difficult-proofs.md` 看是否有类似问题
3. **证明后**: 将关键 API 用法和技巧记录到对应文件
4. **更新**: 修改 any .knowledge 文件后立即提交推送
