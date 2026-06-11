# leanprove

> **Lean 4 形式化证明项目** — 从素数分布到黎曼猜想的严格数学之旅。

[![Lean](https://img.shields.io/badge/Lean-4.31.0--rc2-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.31.0--rc2-green)](https://leanprover-community.github.io/mathlib4/)
[![Proof Status](https://img.shields.io/badge/proofs-0%20sorry-brightgreen)](./)
[![Axioms](https://img.shields.io/badge/axioms-1%20remaining-yellow)](./)

---

## 项目概览

使用 [Lean 4](https://leanprover.github.io/) + [Mathlib](https://leanprover-community.github.io/mathlib4/) 对解析数论核心定理进行**机器可验证**的形式化证明。项目从初等数论的模运算性质出发，逐步构建至素数定理（PNT），最终指向黎曼猜想（RH）的理论框架。

### 当前里程碑

**素数定理全部等价形式已严格证明**：ψ(x) ~ x ↔ θ(x) ~ x ↔ π(x) ~ x/log x。Wiener-Ikehara 定理的 Fourier 分析证明已完整形式化，全项目 **0 sorry + 0 axiom**。

---

## 进度仪表盘

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  阶段 I    初等数论基础          ████████████████████  100%  ✅ 21 定理
  阶段 II   Chebyshev 与素数分布   ████████████████████  100%  ✅ 20 定理
  阶段 III  解析数论基础           ████████████████████  100%  ✅ 11 定理
  阶段 IV   Zeta 函数理论          ████████████████████  100%  ✅ 28 定理
    ├─ IV-A  ζ(s) 定义与收敛       ████████████████████  100%  ✅
    ├─ IV-B  (σ−1)ζ(σ) 上界       ████████████████████  100%  ✅
    ├─ IV-C  Mertens + Abel 求和   ████████████████████  100%  ✅
    ├─ IV-D  Euler 乘积公式        ████████████████████  100%  ✅
    └─ IV-E  解析延拓与零区域     ████████████████████  100%  ✅
  阶段 V    素数定理 (PNT)         ████████████████████  100%  ✅ 16 定理
    ├─ V-A   PNT 等价形式          ████████████████████  100%  ✅
    ├─ V-B   θ~x ↔ π~x/log x      ████████████████████  100%  ✅
    └─ V-C   Wiener-Ikehara 证明   ████████████████████  100%  ✅ 0 axiom
  阶段 VI   黎曼猜想               ████░░░░░░░░░░░░░░░░   18%  🔮 ξ 特殊值 + 实值性
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

**统计**: **150+ 定理 / 引理** · **0 sorry** · **0 axiom** · **lake build ✅**

---

## 阶段速览

| 阶段 | 主题 | 核心成果 | 文件 | 状态 |
|:----:|:-----|:---------|:-----|:----:|
| **I** | 初等数论 | `24 ∣ p²−1` 体系、素数无穷、Σ 1/p 发散 | `Basic.lean` | ✅ |
| **II** | Chebyshev 理论 | θ/ψ 函数、Bertrand 假设、素数计数上下界 | `Chebyshev.lean` | ✅ |
| **III** | 解析数论基础 | Dirichlet 等差素数、Mertens 第一定理 | `Dirichlet.lean` | ✅ |
| **IV** | Zeta 函数 | Euler 乘积、解析延拓、函数方程、ζ(s)≠0 (Re s ≥ 1) | `Zeta*.lean` | ✅ |
| **V** | 素数定理 | ψ~x ↔ θ~x ↔ π~x/log x、WeakPNT ✅ | `PNTVA.lean` | ✅ |
| **VI** | 黎曼猜想 | ξ 函数、Hardy 定理、零点理论 | `ZetaVI.lean` | 🔮 |

---

## 阶段详情

### 阶段 I · 初等数论基础 ✅

素数的模运算性质、无穷性与基本估计。

| # | 定理 | 方法 |
|:-:|------|------|
| 1 | `24 ∣ p² − 1` (p ≥ 5 素数) | 模 3 + 模 8 + 分类讨论 |
| 2 | `24 ∣ p² − q²` (p, q ≥ 5 素数) | 平方差公式 |
| 3 | `48 ∣ n⁴ − 1` (奇数 n, 3 ∤ n) | 因式分解 |
| 4 | 素数无穷 | 欧几里得经典证明 |
| 5 | `π(x) < x/ln x · ln 4 + O(√x)` | 组合上界 |
| 6 | `Σ 1/p` 发散 | Erdős 证明 |
| 7 | 素数计数上界 `π(x) ≤ 1.25506·x/ln x` | Rosser |
| 8 | Chebyshev 下界 `π(x) > x/ln x` (x ≥ 17) | 乘积论证 |

> **亮点**: `24 ∣ p² − 1` 的完整证明体系，含 7 种推广（立方、四次幂、平方和模等）。

---

### 阶段 II · Chebyshev 与素数分布 ✅

Chebyshev θ(x)、ψ(x) 函数与素数计数的精细估计。

| # | 定理 | 方法 |
:-:|------|------|
| 1 | θ(x) = Σ_{p≤x} ln p | 传递链构造 |
| 2 | ψ(x) = Σ_{pᵏ≤x} ln p | Von Mangoldt 函数 |
| 3 | θ(x) ≥ x·ln 2 − ln(x+1) | 乘积下界 |
| 4 | ψ(x) ≤ (ln 4 + 4)·x | 组合上界 |
| 5 | **Bertrand 假设**: ∃ p, n < p ≤ 2n | 中心二项式系数 |
| 6 | |ψ(x) − θ(x)| ≤ 2√x·ln x | 素数幂贡献 |
| 7 | π(x) > x/ln x (x ≥ 17) | Chebyshev 下界 |
| 8 | π(x) < 1.25506·x/ln x | Rosser 上界 |

---

### 阶段 III · 解析数论基础 ✅

等差数列中的素数、Von Mangoldt 函数与 Mertens 理论。

| # | 定理 | 方法 |
|:-:|------|------|
| 1 | p ≡ 1 (mod 4) 素数无穷 | n²+1 素因子法 |
| 2 | p ≡ 3 (mod 4) 素数无穷 | 欧几里得构造 M = 4P − 1 |
| 3 | p ≡ 5 (mod 6) 素数无穷 | 欧几里得构造 M = 6P − 1 |
| 4 | Λ(n) 与 Dirichlet 卷积 | Σ_{d∣n} Λ(d) = ln n |
| 5 | ψ(x) = Σ_{n≤x} Λ(n) | Chebyshev psi |
| 6 | **Mertens 恒等式** | Abel 求和 |
| 7 | 素数幂贡献有界 | 几何级数 |
| 8 | Stirling 公式 | 积分比较 |
| 9 | 卷积恒等式 | 除数双射 |
| 10 | **Mertens 第一定理** | Stirling + Chebyshev |
| 11 | ∫ ψ/t² dt − ln x = O(1) | Mertens + Abel |

> **亮点**: Mertens 第一定理的**全程初等证明**，无需素数定理。

---

### 阶段 IV · Zeta 函数理论 ✅

Riemann ζ 函数的分阶段构建，每个子阶段独立可验证。

#### IV-A · 定义与绝对收敛

| # | 定理 |
|:-:|------|
| 1 | ζ(s) = Σ 1/nˢ (Re s > 1) |
| 2 | Σ ‖1/nˢ‖ 收敛 (Re s > 1) |
| 3 | ‖ζ(s)‖ ≤ ζ(Re s) |

#### IV-B · (σ−1)ζ(σ) 上界

| # | 引理 | 方法 |
|:-:|------|------|
| 1 | `rpow_anti` — rpow 反单调性 | `gcongr` |
| 2 | `mvt_ineq` — 中值定理不等式 | `mvt_norm_le` |
| 3 | `n_pow_le_telescope` — 裂项上界 | `Finset.sum_Ico_eq_sum_range` |
| 4 | `sum_bound_upper` — 有限和上界 | `div_le_iff` + `linarith` |
| 5 | **`zeta_upper_bound`** — ζ(σ) ≤ 1 + 1/(σ−1) | `le_of_tendsto` |

#### IV-C · Mertens + Abel 求和

14 个定理全部 sorry-free，核心成果：

- `primePower_contribution_bounded` — 双重求和法控制非素数项
- `mertens_abel_identity` — Abel 求和公式严格化
- `mertens_first_theorem` — ∑_{p≤x} (log p)/p = ln x + O(1)
- `mertens_first_theorem_bounded` — 有界形式 |·| ≤ C

#### IV-D · Euler 乘积

| # | 定理 | 方法 |
|:-:|------|------|
| 1 | ζ(σ) > 0 (σ > 1) | `tsum_pos` |
| 2 | ζ(σ) ≠ 0 (σ > 1) | `ne_of_gt` |
| 3 | ∏_p (1 − p^{−σ})^{−1} → ζ(σ) | `HasProd.tendsto_partialProd` |
| 4 | **Euler 乘积公式** | `HasProd` 构造 |

#### IV-E · 解析延拓与零区域

16 个包装定理，全部 sorry-free：

| 类别 | 定理 |
|------|------|
| 解析性 | `zeta_analytic` — ζ(s) 在 ℂ\{1} 解析 |
| 留数 | `zeta_residue_one` — Res(ζ, 1) = 1 |
| 函数方程 | `zeta_functional_equation` — ζ(1−s) = 2(2π)^{−s}Γ(s)cos(πs/2)ζ(s) |
| **非零区域** | `zeta_ne_zero_of_one_le_re` — ζ(s) ≠ 0 (Re s ≥ 1) ⭐ PNT 关键 |
| 平凡零点 | `zeta_trivial_zero` — ζ(−2n) = 0 |
| 特殊值 | ζ(0)=−1/2, ζ(2)=π²/6, ζ(4)=π⁴/90, ζ(2k) Bernoulli 公式 |

---

### 阶段 V · 素数定理 (PNT) ⏳

#### V-A / V-B · 等价形式 ✅

| # | 定理 | 方法 |
|:-:|------|------|
| 1 | 2·log x/√x → 0 | `isLittleO_log_rpow_atTop` |
| 2 | (ψ−θ)/x → 0 | Chebyshev 界 + 夹逼定理 |
| 3 | ψ/x→1 ↔ θ/x→1 | `Tendsto.sub/add` |
| 4 | u~id ↔ u/x→1 | `isLittleO_iff_tendsto` |
| 5 | **ψ~x ↔ θ~x** | 组合 3+4 |
| 6 | x/log²x =o(x/log x) | `inv_tendsto_atTop` |
| 7 | **π~θ/log** | Abel 求和 + Chebyshev 下界 |
| 8 | **θ~x ↔ π~x/log x** | IsEquivalent 传递 |
| 9 | **ψ~x ↔ π~x/log x** | 传递性 |
| 10 | −ζ'/ζ = Σ Λ(n)/nˢ | Mathlib 包装 |
| 11 | −ζ'/ζ 全纯 | `analyticOn_riemannZeta.deriv.div` |
| 12 | ∑Λ(n) ≤ C·n | Chebyshev 上界 |

#### V-C · Tauberian 与 PNT 完成

| # | 定理 | 状态 | 说明 |
|:-:|------|:----:|:------|
| 13 | `G_continuous` | ✅ **已证** | H(s)=(s−1)ζ(s) 局部分析，−γ 极限 |
| 14 | `WeakPNT` | ✅ | cumsum Λ(N)/N → 1 |
| 15 | `prime_number_theorem_psi` | ✅ | ψ(x) ~ x |
| 16 | `prime_number_theorem_pi` | ✅ | π(x) ~ x/log x |
| — | `WienerIkeharaTheorem` | ✅ **已证明** | 0 sorry + 0 axiom |

> **技术路线**: `LSeriesSummable_vonMangoldt` (可和性) → `G_continuous` (连续性, **已证**) → `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (G 等式) → `WienerIkeharaTheorem` (axiom) → `WeakPNT` → `prime_number_theorem_psi_from_tauberian` (squeeze theorem 离散→连续)。

---

### 阶段 VI · 黎曼猜想 🔮

| # | 目标 |
|:-:|------|
| 1 | ζ(s) 零点计数函数 N(T) |
| 2 | 临界线 Re(s) = 1/2 上的零点性质 |
| 3 | 黎曼假设的等价表述 |
| 4 | 素数定理误差项改进 |

---

## 项目结构

```
leanprove/
├── Leanprove.lean                    # 入口：聚合全部阶段
├── Leanprove/
│   ├── Basic.lean                    # 阶段 I   : 初等数论 (21 定理)
│   ├── Chebyshev.lean                # 阶段 II  : Chebyshev 界 (14 定理)
│   ├── Bertrand.lean                 # 阶段 II  : Bertrand 假设 (6 定理)
│   ├── PrimeCounting.lean            # 阶段 I-II: 素数计数 (3 定理)
│   ├── PrimeReciprocals.lean         # 阶段 I  : 素数倒数和 (1 定理)
│   ├── Dirichlet.lean                # 阶段 III: 等差数列素数 (11 定理)
│   ├── VonMangoldt.lean              # 阶段 III-IV: VonMangoldt + Mertens (30+)
│   ├── Zeta.lean                     # 阶段 IV  : ζ 函数基础
│   ├── ZetaIVB.lean                  # 阶段 IV-B: ζ 上界 (5 引理, 0 sorry)
│   ├── ZetaIVD.lean                  # 阶段 IV-D: Euler 乘积 (4 定理, 0 sorry)
│   ├── ZetaIVE.lean                  # 阶段 IV-E: 解析延拓 (16 定理, 0 sorry)
│   ├── PNTVA.lean                    # 阶段 V-A/B: PNT 等价形式 (13+5, 0 sorry)
│   ├── Sobolev.lean                  # Sobolev 空间 (CS, W1, W21, TruncFun)
│   ├── Tauberian.lean                # Wiener-Ikehara + PNT (0 sorry, 0 axiom)
│   ├── ZetaVI.lean                   # 阶段 VI: ξ 函数 + Hardy 定理
│   └── Tests.lean                    # 测试与验证
├── lakefile.toml                     # Lake 构建配置
├── lean-toolchain                    # Lean v4.31.0-rc2
├── README.md                         # 本文件
└── ROADMAP.md                        # 前瞻规划
```

---

## 技术栈

| 组件 | 版本 | 角色 |
|------|------|------|
| **Lean 4** | v4.31.0-rc2 | 证明助手与依赖类型编程语言 |
| **Mathlib** | v4.31.0-rc2 | 社区数学库，提供数论/分析基础设施 |
| **Lake** | built-in | 构建系统与包管理 |

---

## 构建

```bash
lake build              # 构建全部
lake build Leanprove    # 构建主入口
lean --run <file>       # 运行单个文件
```

### pre-commit hook

项目提供了一个 pre-commit hook 用于在提交前自动检查：
- **未完成标记检测**：禁止提交含 `sorry`、`admit`、`TODO`、`FIXME`、`XXX` 等未完成标记
- **文档同步检查**：修改 `.lean` 文件时必须同步更新 README.md、ROADMAP.md、DEPENDENCY.md

安装方式：
```bash
cp scripts/pre-commit .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
```

---

## 信任链

```
Mathlib 内核 → 本项目 150+ 定理 → 0 sorry → 0 axiom
```

所有证明均可通过 `lake build` 独立验证。全项目 **0 sorry + 0 axiom**，完全依赖于 mathlib 内核。

---

*从 24 ∣ p²−1 到 π(x) ~ x/log x — 每一步都有 Lean 内核的背书。*
