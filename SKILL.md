name: lean-proof-methodology description: "Lean 4 proof methodology: 三次失败细化todo，当前证明未完成禁止跳下一个，RAG知识库更新" tags: ["lean", "proof", "methodology", "mathlib", "rag"] triggers: - "证明sorry" - "proof sorry" - "fill sorry" - "prove lemma" - "lean build" - "lake build"
Lean 4 证明方法论
核心规则
三次失败必须细化todo，当前证明未完成禁止跳下一个。

RAG 知识库
项目知识库位于 D:\OpenClaw\leanprove\.knowledge\，包含:

mathlib-api.md - Mathlib API 用法记录
proof-patterns.md - 证明模式和技巧
project-structure.md - 项目结构和依赖关系
sorry-inventory.md - 当前 sorry 清单和进展
fourier-transform.md - Fourier 变换相关 API
证明前必须查阅相关知识文件，证明成功后必须更新知识库。

工作流程
1. 分析sorry
读取sorry的上下文（类型签名、已有hypothesis、目标类型）
查阅 .knowledge/ 目录中的相关知识文件
搜索Mathlib中是否有类似定理/引理
2. 第一次尝试
写出最直接的证明策略
编译验证
3. 第二次尝试（如果失败）
分析错误信息
换用不同策略（simp, rw, exact, apply等）
4. 第三次尝试（如果仍失败）
必须停止当前尝试
将证明拆分为子任务写入todo
子任务粒度：单个 have、单个 rw、单个 exact 等原子操作
5. 子任务攻克
逐一证明子任务
子任务如果连续三次失败，继续细化
所有子任务完成后，组合到主文件
6. 推送
编译通过后立即推送
当前sorry完全证明前，禁止跳到下一个sorry
7. 更新知识库
每次证明成功后，将关键 API 用法和技巧记录到 .knowledge/ 对应文件
更新 sorry-inventory.md 跟踪进展
将新发现的证明模式记录到 proof-patterns.md
细粒度todo示例
证明 decay_bounds_key 的三角不等式sorry:
  1a. 证明 h_cast: 1/(4*↑π²) = ↑(1/(4*π²))
  1b. 证明 h_ptwise: ‖f-c*f''‖ ≤ ‖f‖+c*‖f''‖
  1c. 证明 h_lhs_int: LHS可积
  1d. 证明 h_rhs_int: RHS可积
  1e. 证明 h_rhs_eq: ∫(‖f‖+c*‖f''‖) = ∫‖f‖+c*∫‖f''‖
常用Lean 4技巧
Cast处理
push_cast / norm_cast 处理类型转换
field_simp 处理除法
ring_nf 处理环等式（Nat截断减法不适用）
积分相关
integral_mono 比较积分
integral_add 拆分积分
integral_mul_const 提取常数
Integrable.norm 范数可积
Integrable.smul 标量乘法可积
Fourier变换
fourier_deriv: 𝓕(deriv f) = (2πIu) • 𝓕(f)
fourierIntegral_continuous: L¹函数的Fourier变换连续
norm_fourierIntegral_le_integral_norm: ‖𝓕(f)‖ ≤ ∫‖f‖