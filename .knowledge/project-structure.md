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
├── Leanprove.ZetaIVB (ζ函数 IV-B, 184行)
├── Leanprove.ZetaIVD (ζ函数 IV-D, 96行)
├── Leanprove.ZetaIVE (ζ函数 IV-E, 107行)
├── Leanprove.PNTVA (PNT等价形式, 494行)
├── Leanprove.Sobolev (Sobolev空间, 113行)
├── Leanprove.Tauberian (Tauberian定理, 466行)
├── Leanprove.Tests (回归测试, 89行)
├── Leanprove.WienerProof (Wiener-Ikehara证明, 1221行)
│   ├── ⚠️ 29 sorries, 超过 800 行上限
│   └── 依赖: Sobolev, Basic
├── Leanprove.ZetaVI (Hardy定理入口, 25行)
│   ├── Leanprove.ZetaVI.Definitions (定义, 233行, 9 sorries)
│   ├── Leanprove.ZetaVI.Asymptotics (渐近分析, 219行)
│   └── Leanprove.ZetaVI.Hardy (Hardy定理核心, 253行, 5 sorries)
└── Leanprove.ApiCheck (API检查, 39行)
```

## WienerProof.lean 结构

```
WienerProof.lean
├── 基础定义 (cumsum, nabla, nnabla, shift, nterm)
├── W21 空间 (Sobolev W^{2,1})
├── Fourier 变换基础引理 (F_neg, F_add, F_sub, F_mul)
├── fourierIntegral_self_add_deriv_deriv (已证明)
├── decay_bounds_key (已证明)
├── decay_bounds_cor (已证明)
├── continuous_FourierIntegral (已证明)
├── decay_bounds_W21 (待证明)
├── nnabla_bound_aux (部分证明)
├── Wiener-Ikehara 定理
└── PNT 应用
```

## Mathlib 版本

- Lean: v4.31.0-rc2
- Mathlib: v4.31.0-rc2
- Toolchain: leanprover/lean4:v4.31.0-rc2

## 构建命令

```bash
# 编译项目
lake build Leanprove

# 编译单个文件
lake build Leanprove.WienerProof
lake build Leanprove.ZetaVI.Hardy

# 下载 Mathlib 缓存
lake exe cache get

# 直接使用 elan 管理的 lake（Windows）
"C:\Users\35234\.elan\toolchains\leanprover--lean4-v4.31.0-rc2\bin\lake.exe" build
```

## GitHub 仓库

- 地址: https://github.com/shushuzn/leanprove
- 分支: master
