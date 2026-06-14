---
name: lean-proof-methodology
description: "Lean 4 proof methodology: 三次失败细化todo，当前证明未完成禁止跳下一个，RAG知识库更新, 证明规模管控(30行), 文件规模管控(800行)"
tags: ["lean", "proof", "methodology", "mathlib", "rag"]
triggers:
  - "证明sorry"
  - "proof sorry"
  - "fill sorry"
  - "prove lemma"
  - "lean build"
  - "lake build"
---

# Lean 4 证明方法论

## 核心工作流程：RAG 优先 (RAG-First)

**当用户说"按照skill"或"按照skill执行"时，标准流程是：**

1. **第一步：查阅 RAG 知识库**（不是直接开始证明）
   - 查阅 `.knowledge/sorry-inventory.md` 了解当前 sorry 状态
   - 查阅 `.knowledge/mathlib-api.md` 搜索相关 API
   - 查阅 `.knowledge/proof-patterns.md` 搜索类似证明模式
   - 查阅 `.knowledge/bigo-api.md` 搜索 BigO 相关 API（如果涉及渐近分析）
   - 查阅 `.knowledge/nnabla-api.md` 搜索 nnabla/nabla 相关 API（如果涉及序列差分）
   - **查阅 `STYLE.md` 了解代码格式规范**（文件结构、docstring、命名、证明格式）

2. **第二步：判断 RAG 完整性**
   - 如果 RAG 中已有相关 API 和模式 → 直接开始证明（但 RAG 中的引理要先在独立测试中验证）
   - 如果 RAG 缺少相关 API → **必须先用 `grep` 在 Mathlib 源码中搜索并补充到 RAG，然后再开始证明**
   - 用户的明确偏好："如果没有相关内容就先完善RAG" —— 不要跳过 RAG 完善步骤直接尝试证明
   - **STYLE.md 中定义了完整的 mathlib4 规范格式，所有新增代码必须符合该规范**

3. **第三步：开始证明**
   - 先在 `/tmp/test_X.lean` 独立测试中验证策略
   - 编译通过后再应用到主文件

4. **第四步：证明后更新 RAG**
   - 记录新发现的 API、模式、pitfall

**用户原话**："等一下，安装skill，应该先看RAG，如果没有相关内容就先完善RAG" —— 这个顺序是用户的硬性要求。

## RAG 知识库

项目知识库位于 `.knowledge/` 目录，包含:
- `mathlib-api.md` - Mathlib API 用法记录
- `proof-patterns.md` - 证明模式和技巧
- `project-structure.md` - 项目结构和依赖关系
- `sorry-inventory.md` - 当前 sorry 清单和进展
- `fourier-transform.md` - Fourier 变换相关 API
- `difficult-proofs.md` - 困难 proof 的记录和分析
- `bigo-api.md` - BigO/渐近分析 API 完整参考
- `nnabla-api.md` - nnabla/nabla 序列差分 API
- `nnabla_bound_aux-subtasks.md` - nnabla_bound_aux 的子任务分解（参考样本）

**所有具体证明模式、API 参考、pitfall 记录，均已从 skill 移入以上 RAG 文件。skill 仅保留工作流程和方法论。**

## 工作流程

### 0. 第一步：RAG 检查 + 文件规模检查（强制）
- **禁止使用 subagent**：所有证明工作必须由主 agent 直接完成，不要将任务委托给子 agent。Lean 证明需要完整的上下文和项目环境，子 agent 无法有效处理。
- **不要直接开始证明** —— 先查阅 `.knowledge/` 目录
- 如果 RAG 缺少相关内容，先用 `grep` 搜索 Mathlib 源码并补充到 RAG
- 用户的明确偏好："如果没有相关内容就先完善RAG"
- **文件规模检查**（每次添加内容前必须执行）：
  - `wc -l` 检查目标 .lean 文件的行数
  - 若文件 ≥ 800 行：**禁止向该文件新增内容**。新增内容必须放入新文件，新文件通过 `import` 引入原文件
  - 若需拆分已有超大型文件（如 VonMangoldt.lean 1313 行、WienerProof.lean 1221 行）：
    1. 创建新文件 `OriginalName_Part2.lean`，将后半部分内容移入
    2. 原文件末尾添加 `import ...OriginalName_Part2` 保持命名空间连贯
    3. 更新 `Leanprove.lean` 主入口文件，添加对新文件的 import
    4. 更新 `.knowledge/project-structure.md` 反映拆分后的依赖关系

### 1. 分析sorry（RAG 模式）
- 读取sorry的上下文（类型签名、已有hypothesis、目标类型）
- **查阅 `.knowledge/` 目录中的相关知识文件**
- 如果知识库缺少所需 API，用 `grep` 在 Mathlib 源码中搜索并补充到知识库
- 搜索Mathlib中是否有类似定理/引理
- **规模预估**：预估完整证明的行数。若预计超过 **30 行**，立即拆分为子引理（每个 ≤15 行），写入 todo 并在 `.tasks/<name>-subtasks.md` 记录，然后 **跳过第一次尝试，直接进入子任务攻克**。若预计 ≤30 行，正常进入第 2 步。

### 2. 第一次尝试
- 写出最直接的证明策略
- **先在 `/tmp/test_X.lean` 独立测试中验证**
- 编译验证

### 3. 第二次尝试（如果失败）
- 分析错误信息
- 换用不同策略（simp, rw, exact, apply等）
- **必须有明确证据才能换方法**：只有在当前方法有明确证据证明不可行时才能换方法。禁止用"可能"、"也许"、"猜测"等模糊理由。必须先检查当前方法的具体错误信息，确认失败原因后再换。

### 4. 第三次尝试（如果仍失败）
- **必须停止当前尝试，不要尝试第四次。** 用户已多次提醒此规则。
- 将证明拆分为子任务写入 todo
- **同时将子任务分解记录到 `.tasks/<name>-subtasks.md`**
- 子任务粒度：单个 `have`、单个 `rw`、单个 `exact` 等原子操作

### 5. 子任务攻克
- 逐一证明子任务
- 子任务如果连续三次失败，继续细化
- 所有子任务完成后，组合到主文件
- **当前 sorry 完全证明前，禁止跳到下一个 sorry。** 当前证明未完成禁止跳下一个。

### 6. 推送
- 编译通过后立即推送
- 当前sorry完全证明前，禁止跳到下一个sorry

### 7. 更新知识库（RAG 模式）
- **每次证明成功后，将关键 API 用法和技巧记录到 `.knowledge/` 对应文件**
- 更新 `sorry-inventory.md` 跟踪进展
- 将新发现的证明模式记录到 `proof-patterns.md`
- 如果遇到困难，记录到 `difficult-proofs.md`
- **如果发现知识库缺少内容，立即补充**：
  - 用 `grep` 在 Mathlib 源码中搜索相关 API
  - 将 API 用法记录到 `mathlib-api.md`
  - 将证明模式记录到 `proof-patterns.md`
  - 将 BigO 相关 API 记录到 `bigo-api.md`
  - 将 nnabla 相关 API 记录到 `nnabla-api.md`
