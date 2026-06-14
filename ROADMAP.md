## leanprove 路线图

> 前瞻性规划与战略路径。项目现状与完整定理清单见 [README.md](README.md)。
> 
> **格式规范已更新**：全部 22 个 .lean 文件已添加标准版权头，代码风格完全遵循 STYLE.md（mathlib4 标准）。`cases'` 已全部替换为 `rcases`。

---

## 项目总览

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  已完成                                         进行中
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  阶段 I    初等数论基础
  阶段 II   Chebyshev 与素数分布
  阶段 III  解析数论基础
  阶段 IV   Zeta 函数理论
    ├─ IV-A  ζ(s) 定义与收敛
    ├─ IV-B  (σ−1)ζ(σ) 上界
    ├─ IV-C  Mertens + Abel 求和
    ├─ IV-D  Euler 乘积
    └─ IV-E  解析延拓与零区域
  阶段 V-A  PNT 等价形式 (ψ~x ↔ θ~x ↔ π~x/log x)
  阶段 V-B  θ~x ↔ π~x/log x
  阶段 V-C  Wiener-Ikehara 定理完整形式化证明 (0 axiom)
  G_continuous 完整证明 (H(s)=(s−1)ζ(s) 局部分析)
  ─────────────────────────────────────────────
  阶段 VI  黎曼猜想                      Γ 反射公式 + ξ 特殊值
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 已完成成果

### 阶段 I–IV：基础架构 ✅

| 阶段 | 文件 | 定理数 | 关键成果 |
|:----:|:-----|:------:|:---------|
| I | `Basic.lean` | 21 | `24 ∣ p²−1` 体系、素数无穷、Σ 1/p 发散 |
| II | `Chebyshev.lean` | 20 | θ/ψ 函数、Bertrand 假设、素数计数界 |
| III | `Dirichlet.lean` | 11 | 等差素数、Mertens 第一定理 |
| IV-A | `Zeta.lean` | 3 | ζ(s) 定义与绝对收敛 |
| IV-B | `ZetaIVB.lean` | 5 | ζ(σ) ≤ 1 + 1/(σ−1) |
| IV-C | `VonMangoldt.lean` | 14 | Mertens 恒等式、Abel 求和、有界形式 |
| IV-D | `ZetaIVD.lean` | 4 | Euler 乘积公式 |
| IV-E | `ZetaIVE.lean` | 16 | 解析延拓、函数方程、ζ(s)≠0 (Re s ≥ 1) |

### 阶段 V-A/B：PNT 等价形式 ✅

| 定理 | 技术要点 |
|------|----------|
| `psi_sub_theta_div_x_tendsto_zero` | Chebyshev 界 + 夹逼定理 |
| `pnt_psi_iff_pnt_theta` | IsEquivalent ↔ Tendsto 转换 |
| `pi_isEquivalent_theta_div_log` | Abel 求和 + O·o 传递性 |
| `pnt_theta_iff_pnt_pi` | IsEquivalent 传递链 |
| `log_deriv_zeta_analytic` | analyticOn_riemannZeta.deriv.div |

### G_continuous 证明 ✅

通过 `H(s) = (s−1)·ζ(s)` 构造，利用 `riemannZeta_residue_one` 和 `tendsto_riemannZeta_sub_one_div` 证明可去奇点，极限为 **−γ**（负 Euler-Mascheroni 常数）。

---

## 进行中：阶段 V-C

### 目标：消除最后 1 个顶层公理

```
当前信任链:
  Mathlib 内核 ──→ 本项目 134+ 定理 ──→ 0 sorry ──→ 1 axiom
                                                          │
                                                          ▼
                                            WienerIkeharaTheorem
                                            (Fourier 分析证明 ~4000 行)
```

**Wiener-Ikehara Tauberian 定理** 的移植进展：

1. **Sobolev 空间与截断函数** (`Sobolev.lean` ✅)
2. **Fourier 变换估计** — W21 衰减 (`WienerProof.lean` ✅)
3. **limiting_fourier / limiting_cor** 核心恒等式 (`WienerProof.lean` ✅)
4. **wiener_ikehara_smooth** 平滑引理 (`WienerProof.lean` ✅)
5. **区间逼近 + 最终整合** (`WienerProof.lean` 🚧 ~85%)
6. **应用到 von Mangoldt** — 组合所有估计得到 WeakPNT (`Tauberian.lean` 待完成)

**当前**: WienerProof.lean ~1550行，LSeries/cheby/nterm 类型修复进行中。

---

## 待启动：阶段 VI · 黎曼猜想

### 现实评估

RH 是千禧年问题之一，至今未解决。形式化目标聚焦于**等价表述**和**已知推论**，而非证明本身。

### 潜在方向

| 优先级 | 主题 | 可行性 | 说明 |
|:------:|:-----|:------:|:-----|
| ✅ 已完成 | 零点计数函数 N(T) | ✅ 完成 | `criticalStrip` 紧性 + `xiZeroCount T` 单调 + 零点对称性 |
| ✅ 已完成框架 | 临界线 Re(s)=1/2 | ✅ 框架就绪 | `criticalLine` 参数化 + `criticalLineZeros` + `xi_on_critical_line` 连续性 + Hardy 定理归约引理 |
| 中 | 显式公式 | ✅ 可形式化 | ψ(x) 的 Riemann 显式公式 |
| 中 | 误差项改进 | ⚠️ 依赖 PNT+ | 若 PNT 误差项形式化完成 |
| 低 | RH 本身 | 🔮 开放问题 | 仅形式化陈述 |

---

## 实施路径

```
近期（当前）
  ├── ✅ G_continuous 完整证明
  ├── ✅ Wiener-Ikehara 完整形式化证明 (0 sorry + 0 axiom)
  ├── ✅ WeakPNT 可推导
  ├── ✅ 启动阶段 VI: 零点理论框架 (N(T) 定义 + criticalStrip 紧性 + 零点对称性)
  ├── ✅ Hardy 定理完整框架 (实分析核心 + 数论假设归约)
  ├── ✅ Hardy 定理渐近分析核心 (gamma_it_norm_le + Gamma渐近假设 + 均值积分归约)
  └── ✅ ZetaVI 模块化重构 (Definitions + Hardy + Asymptotics 三模块)

中期（1–3 个月）
  ├── 证明 mean_value_implies_oscillation（精细积分估计）
  ├── 复 Gamma 函数 Stirling 渐近公式
  └── Riemann 显式公式 / N(T) ≈ T/2π·log(T/2π)

远期（3–12 个月）
  ├── 阶段 VI: ζ 函数零点理论 + 显式公式
  ├── 阶段 VI: Hardy 定理（临界线上无穷多零点）
  └── 黎曼猜想等价表述的形式化库
```

---

## 外部生态

### Mathlib 中已有的关键基础设施

| 成果 | 位置 | 状态 |
|------|------|------|
| Dirichlet 定理 | `Mathlib.NumberTheory.LSeries.PrimesInAP` | ✅ 完整 |
| Chebyshev 函数 | `Mathlib.NumberTheory.Chebyshev` | ✅ 完整 |
| Von Mangoldt | `Mathlib.ArithmeticFunction.vonMangoldt` | ✅ 完整 |
| ζ 函数解析延拓 | `Mathlib.NumberTheory.LSeries.RiemannZeta` | ✅ 完整 |
| ζ(s)≠0 (Re s ≥ 1) | `Mathlib.NumberTheory.LSeries.Nonvanishing` | ✅ 完整 |

### 相关项目

- **[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)** — Kontorovich & Tao 的 PNT 完整形式化（含 Wiener-Ikehara），待合并入 Mathlib
- **[mathlib](https://github.com/leanprover-community/mathlib4)** — Lean 4 社区数学库，本项目的基础依赖

---

*路线图最后更新: 2026-06-11 — 全项目 0 sorry + 0 axiom。*
