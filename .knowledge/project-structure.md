# 项目结构

## 文件依赖关系

```
Leanprove.lean (主入口)
├── Leanprove.Basic (基础数论, 677行)
├── Leanprove.Bertrand (Bertrand假设, 86行)
├── Leanprove.Chebyshev (Chebyshev函数, 308行)
├── Leanprove.Dirichlet (Dirichlet定理, 527行)
├── Leanprove.PrimeCounting (素数计数, 174行)
├── Leanprove.PrimeReciprocals (素数倒数和, 35行)
├── Leanprove.VonMangoldt (Von Mangoldt函数, 1313行)
│   └── ⚠️ 超过 800 行上限，需拆分
├── Leanprove.MathlibTest (Mathlib测试, 5行)
├── Leanprove.ZetaUpperBound (ζ 上界, 184行)
├── Leanprove.EulerProduct (Euler 乘积, 96行)
├── Leanprove.ZetaAnalyticContinuation (解析延拓与零区域, 107行)
├── Leanprove.PrimeNumberTheorem (PNT 等价形式, 494行)
├── Leanprove.Sobolev (Sobolev空间, 113行)
├── Leanprove.Tauberian (Tauberian定理, 466行)
├── Leanprove.Tests (回归测试, 89行)
├── Leanprove.WienerIkehara (Wiener-Ikehara证明, 1221行)
│   ├── ⚠️ 29 sorries, 超过 800 行上限
│   └── 依赖: Sobolev, Basic
├── Leanprove.CriticalLine (Hardy定理入口, 25行)
│   ├── Leanprove.CriticalLine.Definitions (定义, 233行, 9 sorries)
│   ├── Leanprove.CriticalLine.Asymptotics (渐近分析, 219行)
│   └── Leanprove.CriticalLine.Hardy (Hardy定理核心, 253行, 5 sorries)
└── Leanprove.ApiCheck (API检查, 39行)
```

## WienerIkehara.lean 结构

WienerIkehara.lean 提供完整的 Wiener-Ikehara Tauberian 定理证明。
分为以下主要节段：

| 节段 | 行号 | 内容 |
|------|------|------|
| Basic discrete analysis | 60+ | cumsum, nabla, nnabla 定义和基本引理 |
| W21 auxiliary | 190+ | W21 函数的可积性和可微性 |
| Fourier transform | 230+ | Fourier 变换的衰减估计 |
| Asymptotic estimates | 430+ | nnabla 渐近分析和对数估计 |
| Chebyshev bound | 720+ | Chebyshev 有界性的 Fourier 分析 |
| Fourier inversion | 870+ | Fourier 反转和极限引理 |
| Wiener-Ikehara estimates | 950+ | 光滑 Wiener-Ikehara 估计和区间定理 |

## 关键模块引用

- `Leanprove.WienerIkehara` — Wiener-Ikehara 定理完整证明
- `Leanprove.Tauberian` — Wiener-Ikehara → PNT 应用
- `Leanprove.Sobolev` — W21 空间定义和基本性质
