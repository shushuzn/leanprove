# F_add 子任务分解

## 背景

`F_add` 证明 `𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x`，即 Fourier 变换的线性性。

**失败次数**: 4+ 次（已触发 skill 的"三次失败细化"规则）

## 失败原因分析

1. `VectorFourier.fourierIntegral_add` 在 root namespace 不存在
2. `Integrable.mono` 签名理解错误：实际是 `(hg : Integrable g) (hf : AEStronglyMeasurable f) (h : ...)`
3. `fun_prop` 无法证明 `AEStronglyMeasurable (fun v => 𝐞 (-(inner ℝ v x)) • f v)` — `Circle.smul` 不在 `fun_prop` 知识库中
4. 直接 `apply Integrable.mono hf` 时，Lean 无法推断目标函数类型

## 正确方法

来自 `Mathlib/Analysis/Fourier/Inversion.lean:63`：
```lean
AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop)) hf.1
```

## 原子子任务

### 1a. 证明 `h_cont : Continuous fun v => 𝐞 (-(inner ℝ v x))`
- `𝐞` 是 `Real.fourierChar : ℝ → Circle`，连续
- `inner ℝ v x` 连续，neg 连续
- 用 `Continuous.comp` 组合

### 1b. 证明 `hae_scalar : AEStronglyMeasurable (fun v => 𝐞 (-(inner ℝ v x)))`
- 用 `Continuous.aestronglyMeasurable h_cont`

### 1c. 证明 `hae : AEStronglyMeasurable (fun v => 𝐞 (-(inner ℝ v x)) • f v)`
- 用 `AEStronglyMeasurable.smul hae_scalar hf.1`

### 1d. 证明 `h_norm : ∀ v, ‖𝐞 (-(inner ℝ v x)) • f v‖ = ‖f v‖`
- `norm_smul` 给出 `‖c • z‖ = ‖c‖ * ‖z‖`
- 需要 `‖𝐞 (...)‖ = 1`（Circle 元素范数为 1）
- 用 `CStarRing.norm_of_mem_unitary` 或 `simp [norm_smul, ...]`

### 1e. 证明 `h_bound : ∀ᵐ v, ‖𝐞 (-(inner ℝ v x)) • f v‖ ≤ ‖f v‖`
- 用 `Filter.Eventually.of_forall` + `h_norm` + `le_refl`

### 1f. 组合 `hf' : Integrable (fun v => 𝐞 (-(inner ℝ v x)) • f v)`
- 用 `Integrable.mono hf hae h_bound`

### 1g. 同理证明 `hg'`
- 同 1a-1f，将 `f` 换成 `g`

### 1h. 最终 `integral_add hf' hg'`
- 用 `integral_add` 得证

## 测试文件

在 `/tmp/test_F_add.lean` 中逐个测试子任务，编译通过后再应用到主文件。

## 记录到 RAG

- `Integrable.mono` 签名（正确版本）
- `AEStronglyMeasurable.smul` 模式
- `Circle` 元素范数为 1 的证明方法
