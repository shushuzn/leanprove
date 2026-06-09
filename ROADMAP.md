## leanprove 项目路线图

### 项目现状

leanprove 是一个使用 Lean 4 + Mathlib 进行数论形式化证明的项目。目前完成了阶段 1-3 的核心工作, 共 58 个定理, **零 sorry**。

已完成的里程碑:

- **阶段 1** (素数分布基础): 围绕 `24 | p² - 1` 的原创证明体系, 25 个定理
- **阶段 2** (Chebyshev 理论): Chebyshev 函数、π(x) 界限、Bertrand 假设、素数倒数发散, 26 个定理
- **阶段 3** (等差数列素数, 部分): p ≡ 1 和 p ≡ 3 (mod 4) 的素数无穷性, 6 个定理
- **代码清理**: 消除了跨文件重复定理、冗余证明和重复文档块

---

### Mathlib 中已有的关键结果

在推进后续阶段前, 了解 Mathlib 中已有的成果至关重要。以下发现在本项目的调研中确认:

**Dirichlet 定理 (完整)**: `Mathlib.NumberTheory.LSeries.PrimesInAP` 中的 `Nat.forall_exists_prime_gt_and_modEq` 已证明完整的 Dirichlet 定理——对任意 q ≠ 0 和 gcd(a,q) = 1, 存在无穷多素数 p ≡ a (mod q)。这意味着阶段 3 的完整目标在 Mathlib 中已经解决。

**p ≡ 1 (mod k)**: `Mathlib.NumberTheory.PrimesCongruentOne` 中的 `Nat.exists_prime_gt_modEq_one` 用分圆多项式方法单独证明了此特殊情形。

**素数计数函数**: Mathlib 有 `Nat.primeCounting` 和 `Nat.tendsto_primeCounting` (π(x) → ∞)。

**Chebyshev 函数**: Mathlib 有完整的 θ(x)、ψ(x) 定义, 以及 Chebyshev 界 (ln2 ≤ liminf ≤ limsup ≤ ln4)。

**尚未在 Mathlib 中形式化的关键结果** (阶段 4-6 所需):

- ζ 函数的解析延拓 (仅有 Re(s) > 1 的定义)
- ζ(1+it) ≠ 0 (PNT 的关键步骤)
- PNT 本身 (π(x) ~ x/ln(x))
- ζ 函数的函数方程
- 零点计数函数 N(T) 和 Hadamard 乘积
- 黎曼猜想的任何非平凡结果

---

### 阶段 3 的后续方向

虽然完整 Dirichlet 定理已在 Mathlib 中, 但本项目的阶段 3 仍有扩展空间:

**补充更多初等证明**。当前只有 p ≡ 3 (mod 4) 的原创证明。可以增加:

- p ≡ 5 (mod 6) 素数无穷多 (欧几里得式构造)
- p ≡ 1 (mod 4) 的初等证明 (不依赖分圆多项式, 用 n² + 1 的素因子方法)
- 算术级数中素数的 Dirichlet 密度 (作为 Mathlib 完整定理的推论提取)

**加强 `infinite_prime_pairs`**。Bertrand.lean 中的此定理使用了 p = q, 可以强化为要求 p ≠ q。

---

### 阶段 4: 素数定理 (PNT)

**目标**: 证明 π(x) ~ x/ln(x), 即 lim π(x)·ln(x)/x = 1。

**Mathlib 现状**: 这是目前最大的缺口。需要的基础设施包括:

- 黎曼 ζ 函数的解析延拓 (Mathlib 有 `RiemannZeta` 模块, 但仅有 Re(s) > 1 的定义)
- ζ(s) 在 Re(s) = 1 上不消失
- 复分析工具: 围道积分、留数定理、Mellin 变换、Perron 公式
- Wiener-Ikehara 定理 (或 Newman/Zagier 的简化证明路径)

Mathlib 的复分析部分 (`Mathlib.Analysis.Complex`) 在持续增长, 但距离支撑 PNT 还有显著差距。

**建议路线**:

1. 完善复分析基础设施 (围道积分、留数定理), 作为向 Mathlib 的 PR 贡献
2. ζ 函数解析延拓到 Re(s) > 0 (除了 s=1 处的单极点)
3. 证明 ζ(1+it) ≠ 0 (经典 Hadamard/de la Vallée Poussin 论证)
4. 形式化 Tauber 定理 (Wiener-Ikehara 或 Newman)
5. 组合为 PNT

**替代策略**: Selberg-Erdős 初等证明 (不使用复分析), 但需要大量关于 Λ(n) 的组合估计, 在 Lean 中同样不轻松。

---

### 阶段 5: ζ 函数与零点理论

**目标**: 研究 ζ(s) 的非平凡零点分布。

**依赖**: 阶段 4 的全部基础设施, 加上复 Gamma 函数的完整理论、ζ 函数的函数方程、整函数的 Hadamard 因式分解定理。

**建议路线**:

1. 补全 ζ 函数的函数方程证明
2. 证明 N(T) ~ (T/2π)·ln(T/2π) - T/2π (零点计数渐近公式)
3. 推导 Hadamard 乘积: ξ(s) = e^{A+Bs} ∏_ρ (1 - s/ρ)e^{s/ρ}
4. 建立 von Mangoldt 显式公式 (素数分布与零点的桥梁)

---

### 阶段 6: 黎曼猜想

**目标**: 陈述并 (尝试) 证明黎曼猜想: ζ(s) 的所有非平凡零点在 Re(s) = 1/2 上。

**现实评估**: 黎曼猜想是 Clay 研究所七大千禧年问题之一, 至今未解决。在 Lean 中形式化陈述是可行的, 但证明需要数学本身的突破。

**可以做的事情**:

- 形式化 RH 的等价表述 (Li 准则、Nyman-Beurling 准则)
- 证明 Hardy 定理 (临界线上有无穷多个零点)
- 形式化 RH 的推论 (素数分布最优误差项 π(x) = Li(x) + O(√x · ln x))
- 零点密度估计的已知结果

---

### 推荐的实施顺序

```
近期
  ├── 补充 p ≡ 1 (mod 4) 的初等证明 (n² + 1 素因子方法)
  ├── 加强 infinite_prime_pairs (要求 p ≠ q)
  ├── 扩展 PrimeReciprocals.lean (Mertens 定理目标)
  └── 添加 Tests.lean 回归测试文件

中期
  ├── 复分析基础设施补全 (围道积分、留数定理)
  ├── ζ 函数解析延拓
  └── ζ(1+it) ≠ 0 的证明

远期
  ├── 素数定理 (PNT)
  ├── ζ 函数零点理论
  └── 黎曼猜想 (陈述与已知结果)
```

---

### 对 Mathlib 社区的建议

阶段 4 以后的工作高度依赖 Mathlib 中尚不存在的基础设施。建议以向 Mathlib 贡献 PR 的方式推进, 特别是复分析工具和 ζ 函数理论。这样既能推进 leanprove 项目, 又能让整个社区受益。
