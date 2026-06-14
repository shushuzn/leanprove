# Leanprove RAG 知识库

本目录存储项目证明过程中积累的知识，用于提高后续证明效率。

## 索引

### API 参考（每条含 Import/签名/说明/Pitfall）

| 文件 | 主题 | 行数 |
|------|------|------|
| `integral-api.md` | 积分相关 API（integral_mono, Integrable.*, AEStronglyMeasurable） | ~93 |
| `fourier-api.md` | Fourier 变换 API（fourier_deriv, fourierIntegral_continuous） | ~37 |
| `contdiff-api.md` | 可微性/连续性 API（ContDiff, CS→W21, 三角不等式模式） | ~77 |
| `bigo-api.md` | BigO/渐近分析 API（IsBigO.*, 项目自定义引理, 组合模式） | ~231 |
| `log-api.md` | 对数 API（Real.log 系列, log bound 模式, log BigO 引理） | ~110 |
| `norm-cast-api.md` | 范数/cast API（norm_real, norm_mul, norm_add_le, cast 模式） | ~68 |
| `division-api.md` | 除法 API（div_sub_one, one_lt_div, lt_div_iff₀'） | ~41 |

### 模式与 Pitfalls

| 文件 | 主题 | 行数 |
|------|------|------|
| `proof-patterns.md` | 证明模式与 Pitfalls（rw 安全、field_simp、linarith 等） | ~99 |
| `nnabla-api.md` | nnabla/nabla 序列差分 API（新格式） | ~55 |

### 项目结构

| 文件 | 主题 | 行数 |
|------|------|------|
| `fourier-transform.md` | 项目 Fourier 衰减定理（decay_bounds_key, decay_bounds_cor 等） | ~94 |
| `project-structure.md` | 项目文件、依赖关系、构建命令 | ~76 |
| `difficult-proofs.md` | 困难 proof 记录和分析 | ~39 |
| `sorry-inventory.md` | 当前 sorry 清单和进展 | ~31 |

> 子任务分解文件（`F_add-subtasks.md`、`nnabla_bound_aux-subtasks.md`）已移至 `.tasks/` 目录。

## 条目格式规范

所有 API 条目必须遵循以下格式：

```markdown
## API/模式名称

**Import**: `Mathlib.XXX.YYY` — 如果没有明确的 import 路径则写"项目自定义引理"
**签名**:
```lean
theorem lemma_name (args...) : result_type := ...
```
**说明**: 一句话说明何时用、做什么。（可选，签名自明则可省略）
**Pitfall**: 常见错误或注意事项。（可选）
```

### 格式规则

1. **层级**: 每个 API 一条 `##`，不用 `###`。`#` 只用于文件标题。
2. **字段顺序**: `**Import**` → `**签名**` → `**说明**` → `**Pitfall**`，不存在的字段跳过。
3. **代码块**: 签名用 ` ```lean `，示例代码也相同。代码块内不写 `--` 注释描述（标题已说明）。
4. **简洁**: 不重复标题已在说明的内容。Pitfall 只说"不能做什么"和"应该做什么"。
5. **文件大小**: 每个 `<200` 行。超过时按主题拆分。
