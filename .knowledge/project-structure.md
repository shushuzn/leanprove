# 项目结构

## 文件依赖关系

```
Leanprove.lean (主入口)
├── Leanprove.Basic (基础数论)
├── Leanprove.Bertrand (Bertrand假设)
├── Leanprove.Chebyshev (Chebyshev函数)
├── Leanprove.Dirichlet (Dirichlet定理)
├── Leanprove.PrimeCounting (素数计数)
├── Leanprove.PrimeReciprocals (素数倒数和)
├── Leanprove.VonMangoldt (Von Mangoldt函数)
├── Leanprove.MathlibTest (Mathlib测试)
├── Leanprove.ZetaIVB (ζ函数 IV-B)
├── Leanprove.ZetaIVD (ζ函数 IV-D)
├── Leanprove.ZetaIVE (ζ函数 IV-E)
├── Leanprove.PNTVA (PNT等价形式)
├── Leanprove.Sobolev (Sobolev空间)
├── Leanprove.Tauberian (Tauberian定理)
└── Leanprove.Tests (回归测试)
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

# 下载 Mathlib 缓存
lake exe cache get
```

## GitHub 仓库

- 地址: https://github.com/shushuzn/leanprove
- 分支: master
