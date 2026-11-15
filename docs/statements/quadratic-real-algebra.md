# 完整实二次展开与零锥规范消去

本轮承接原文 `paper/burnett.tex` 第432–463行，SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。已有实非特征片段见[ricci-symbol.md](ricci-symbol.md)。本页记录并行试运行的新增数学交付；父项F06仍部分完成，当前进度以scope为准。

## 实际对象与共用定义

指标仍为 `Fin 4`，所有分量取实数。`G`表示逆度量的分量参数，`k,l`为协变二张量分量。`IsSymmetricTensor`明写全部分量的对称性。升指标、Ricci符号、规范张量及c、B沿用原有 `RicciSymbol.lean`，没有换成Euclidean收缩。

共享模块 `QuadraticDefs.lean` 定义所有有序指标的实双线性收缩

$$
\langle k,l\rangle_G=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}l_{cd},
\qquad (k^2)_{bc}=\sum_a k_b{}^a k_{ac},
$$

$$F_G(k,l)=\langle k,l\rangle_G-\tfrac12\operatorname{tr}_Gk\operatorname{tr}_Gl.$$

这尚不是复Hermitian定义。完整展开适用于任意实对称G、k；交叉消去在下文的额外零锥核条件下成立。两者均不需要非退化性或签名；取G为原文真实逆Lorentz度量即可逐点应用。几何对象求逆/坐标自然性及零标架商正性的Lean桥接仍未由此完成。

## 四项新增交付

| 清单ID | 实际声明 | 原文 |
| --- | --- | --- |
| `quadratic:full-real-expansion` | `Burnett.RicciSymbol.four_quadraticSymbol_expansion` | 447–448 |
| `quadratic:null-kernel-constraint` | `Burnett.RicciSymbol.null_kernel_iff_contracted` | 454 |
| `quadratic:null-real-formula` | `Burnett.RicciSymbol.quadraticSymbol_eq_physicalPairing_of_null_kernel` | 454–457 |
| `quadratic:null-real-gauge-cross` | `Burnett.RicciSymbol.physicalPairing_pureGauge_eq_zero_of_null_kernel` | 459–463 |

对称G、k下，第一项没有Ricci核或零锥前提，实际证明完整恒等式

$$
4B_{bc}(k,k)=\xi_b\xi_c\langle k,k\rangle_G+2q_bq_c
-2s(k^2)_{bc}-t(\xi_bq_c+\xi_cq_b-sk_{bc}).
$$

第二项仅需 $\xi\ne0$ 和 $s=0$，即使G、k不对称，也有

$$\mathcal R_\xi(k)=0\quad\Longleftrightarrow\quad q=t\xi/2.$$

它从非零协向量选择一个存在的非零分量，没有预设某个固定坐标分量非零。原文单位余球条件保证非零。去掉s=0后该等价一般不成立。

第三项是主代理实际合并两条分支得到的公式：对称G、k、$\xi\ne0$、$s=0$、$\mathcal R_\xi(k)=0$ 时

$$B_{bc}(k,k)=\tfrac14\xi_b\xi_cF_G(k,k).$$

第四项在同一零锥核条件下，对任意实v与 $\ell=\xi\otimes v+v\otimes\xi$ 证明

$$F_G(k,\ell)=0.$$

其证明分别建立对外积的收缩、对称k下的规范收缩以及对称G下的规范迹公式，再使用核约束。没有把交叉消去作为输入，也没有只证明纯规范自身配对为零。

## 实现、证据与剩余义务

两个实现代理分别独占 `QuadraticExpansion.lean` 与 `NullKernel.lean`，共享定义由主代理先构建后固定版本。首个冻结零锥结果先进入独立回读，分支继续完成交叉消去；另一分支同时完成B展开。主代理在 `NullQuadratic.lean` 中作真实拼接，合并版本完整库构建已通过。

源码定位：

- [共用定义](../../Burnett/Algebra/QuadraticDefs.lean)
- [完整实展开](../../Burnett/Algebra/QuadraticExpansion.lean)
- [零锥核及实规范交叉](../../Burnett/Algebra/NullKernel.lean)
- [合并的零锥公式](../../Burnett/Algebra/NullQuadratic.lean)

实际编译、类型、公理及独立回读证据保存在 `.project-verification/parallel-pilot/`。本页不把实现者的编译结果冒充独立复核；最终检查与确认状态见[工程复核](../formalization/review.md)及scope。

仍未完成：实二次式的一般极化与复Hermitian扩展、物理商非负性及一般Lorentz零标架桥接、正Hermitian测度密度的应用，以及F04/F05/F07分析和测度闭合。17项原文编号结果和两个另已批准的未编号目标仍未完成，作者数学对应确认保持待定。
