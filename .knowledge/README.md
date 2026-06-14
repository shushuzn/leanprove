# Leanprove RAG 知识库

本目录存储项目证明过程中积累的知识，用于提高后续证明效率。

## 索引

### API 参考（每条含 Import/签名/说明/Pitfall）

| 文件 | 主题 | 行数 |
|------|------|------|
| `integral-api.md` | 积分相关 API（integral_mono, Integrable.*, AEStronglyMeasurable） | ~60 |
| `fourier-api.md` | Fourier 变换 API（fourier_deriv, fourierIntegral_continuous） | ~30 |
| `contdiff-api.md` | 可微性/连续性 API（ContDiff, HasCompactSupport, CS→W21） | ~40 |
| `bigo-api.md` | BigO/渐近分析 API（IsBigO.*, 项目自定义引理, 组合模式） | ~180 |
| `log-api.md` | 对数 API（Real.log 系列, log bound 模式, log BigO 引理） | ~100 |
| `norm-cast-api.md` | 范数/cast API（norm_real, norm_mul, norm_add_le, cast 模式） | ~80 |
| `division-api.md` | 除法 API（div_sub_one, one_lt_div, lt_div_iff₀'） | ~30 |

### 模式与 Pitfalls

| 文件 | 主题 | 行数 |
|------|------|------|
| `proof-patterns.md` | 证明模式与 Pitfalls（rw 安全、field_simp、linarith 等） | ~90 |
| `nnabla-api.md` | nnabla/nabla 序列差分 API | ~78 |

### 项目特定

| 文件 | 主题 | 行数 |
|------|------|------|
| `fourier-transform.md` | 项目 Fourier 衰减定理（decay_bounds_key, decay_bounds_cor 等） | ~94 |
| `project-structure.md` | 项目文件、依赖关系、构建命令 | ~76 |
| `sorry-inventory.md` | 当前 sorry 清单和进展 | ~31 |
| `difficult-proofs.md` | 困难 proof 记录和分析 | ~39 |
| `F_add-subtasks.md` | F_add 子任务分解 | ~61 |
| `nnabla_bound_aux-subtasks.md` | nnabla_bound_aux 子任务分解 | ~93 |

## 使用规则

1. **证明前**: 查阅 `bigo-api.md` / `log-api.md` / `integral-api.md` 找 API，查阅 `proof-patterns.md` 查 Pitfall
2. **证明中**: 遇到困难查阅 `difficult-proofs.md` 看是否有类似问题
3. **证明后**: 将新发现的 API 和模式记录到对应文件
4. **格式**: 所有 API 条目使用 `## 名称` → **Import** / **签名** / **说明** / **Pitfall** 结构
