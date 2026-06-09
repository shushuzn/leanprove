# leanprove

Lean 4 数学证明项目 — 从素数分布到黎曼猜想的探索之旅

## 当前状态

本项目使用 Lean 4 + Mathlib 形式化证明数论定理，当前聚焦于素数模运算性质。

### 核心定理

**主定理**: 对所有素数 p ≥ 5，24 整除 p² - 1

| 定理 | 陈述 | 状态 |
|------|------|------|
| prime_ge_five_sq_sub_one_dvd | 24 \| p² - 1 | ✅ |
| prime_ge_five_mod_six | p ≡ 1 或 5 (mod 6) | ✅ |
| prime_sq_diff_dvd_24 | 24 \| p² - q² | ✅ |
| gcd_pm1_eq_two | gcd(p-1, p+1) = 2 | ✅ |
| lcm_pm1_eq_half_mul | lcm(p-1,p+1) = (p-1)(p+1)/2 | ✅ |
| prime_sq_mod_twelve | p² ≡ 1 (mod 12) | ✅ |
| prime_sq_sum_mod_24 | p² + q² ≡ 2 (mod 24) | ✅ |
| prime_sq_sum_mod_8 | p² + q² ≡ 2 (mod 8) | ✅ |

### 推广定理

| 定理 | 陈述 | 状态 |
|------|------|------|
| odd_not_three_sq_sub_one_dvd | 24 \| n² - 1 (奇数, 3∤n) | ✅ |
| odd_not_three_cubed_sub_self_dvd | 24 \| n³ - n | ✅ |
| odd_not_three_fourth_sub_one_dvd | 48 \| n⁴ - 1 | ✅ |

## 路线图: 通向黎曼猜想

### 阶段 1: 素数分布基础 ✅

- [x] 素数模 6 分类 (p ≡ 1 或 5 mod 6)
- [x] 平方差整除性 (24 | p² - 1)
- [x] 相邻因子的 gcd/lcm 结构
- [x] 模 12、模 24、模 8 的平方和

### 阶段 2: 素数计数函数

- [ ] Chebyshev 函数 θ(x) = Σ_{p≤x} ln(p)
- [ ] 素数计数函数 π(x) 的定义
- [ ] Chebyshev 不等式: c₁ x/ln(x) < π(x) < c₂ x/ln(x)
- [ ] Bertrand 假设: 对所有 n ≥ 1，存在素数 p 满足 n < p < 2n

### 阶段 3: Dirichlet 定理

- [ ] 等差数列中素数的无穷性
- [ ] Dirichlet L-函数 L(s, χ) 的定义
- [ ] L(1, χ) ≠ 0 的证明
- [ ] 素数在等差数列中的分布

### 阶段 4: 素数定理

- [ ] ζ 函数的 Euler 乘积: ζ(s) = ∏_p (1 - p^{-s})^{-1}
- [ ] ζ 函数的解析延拓
- [ ] ζ 函数的函数方程
- [ ] 素数定理: π(x) ~ x/ln(x)
- [ ] 等价形式: ψ(x) ~ x

### 阶段 5: ζ 函数与零点

- [ ] 非平凡零点的存在性
- [ ] 零点计数函数 N(T)
- [ ] 零点密度估计
- [ ] Hardy 定理: 无穷多个零点在 Re(s) = 1/2 上
- [ ] Selberg 筛法基础

### 阶段 6: 黎曼猜想

- [ ] 黎曼猜想的精确形式化
- [ ] 临界线定理的强化版本
- [ ] 零点分布的精细结构
- [ ] 黎曼猜想的证明 (需要全新数学工具)

## 项目结构

```
leanprove/
├── Leanprove.lean           # 入口文件
├── Leanprove/
│   ├── Basic.lean           # 核心定理 (25+ 定理)
│   └── MathlibTest.lean     # Mathlib 功能验证
├── ARCHITECTURE.txt         # 定理架构图
├── lakefile.toml            # 构建配置
├── lean-toolchain           # Lean 版本
└── README.md                # 本文件
```

## 技术栈

- **语言**: Lean 4 (v4.31.0-rc2)
- **数学库**: Mathlib (v4.31.0-rc2)
- **关键工具**: omega, ring_nf, simp, decide
- **构建系统**: Lake

## 构建

```bash
lake build Leanprove
```

## 参考文献

1. Hardy & Wright, *An Introduction to the Theory of Numbers*
2. Apostol, *Introduction to Analytic Number Theory*
3. Davenport, *Multiplicative Number Theory*
4. Iwaniec & Kowalski, *Analytic Number Theory*
5. Lean 4 Mathlib: https://leanprover-community.github.io/mathlib4/
6. Riemann Hypothesis on Clay Millennium: https://www.claymath.org/millennium-problems/riemann-hypothesis/

## 许可证

本项目中的数学证明是人类知识的共同财富。
