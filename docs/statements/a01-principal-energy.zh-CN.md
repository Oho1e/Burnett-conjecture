# A01. 对称能量配对中的 Lipschitz 系数

[英文阅读副本](a01-principal-energy.en.md)

两条 Lebesgue 声明对应[锁定引理](../../paper/burnett.tex#L566-L575)中的不等式。
矩阵系数版本也见第 595–599 行。两条固定图密度声明对应第 591 行的说明，
使用原文第 524–529 行的嵌套截断设置。

固定一阶、适当支撑的矩阵左量子化 B，使用原文的 Lebesgue 配对和固定欧氏场内积
表达形式对称性。输入 u 由有限个紧支光滑复 Schwartz 分量表示。标量系数 r 光滑、
实值、对两个微分指标对称，并在场指标上作标量乘法。各项系数值的本质界 U 和一阶
Fréchet 导数的本质界 L 给出系数范数约定 U + L。原配对的两倍虚部绝对值被
C(U + L) 乘以坐标 H¹ 范数的平方控制。场的范数包含其值及四个坐标偏导。
常数随固定 B 先于系数和场选取。

矩阵系数声明在互换两个微分指标时取 Hermitian 转置。B 在每个分量上使用同一完整
标量符号。选择常数时场的维数固定。显式的全符号假设包括联合光滑性、统一频率和
纯底变量导数半范数、原符号及其四个首阶坐标导数符号的一阶混合半范数，以及原算子核
关系的适当支撑。估计使用实际 Fourier 作用与坐标偏导。紧底集核估计、分解与全局
拼接在 Lean 内闭合 Lipschitz L² 交换子。

密度声明使用固定坐标图内的正光滑密度和固定嵌套紧截断。原 B 对图内加权紧支测试
形式对称。正平方根延拓及准确的 Fourier 截断表示把原测试的加权配对化为 Lebesgue
配对，右端 H¹ 保持原文的坐标范数约定。常数可依赖固定密度与截断。

四条声明及其原文对应已通过独立复核。原暂存库原生编译零错误，有四条未使用段变量的检查提示。原文算子类及具体下游 Weyl 作用还须接到完整左符号作用。

## 已登记的 Lean 声明

- `Burnett.Analysis.CarlesonEmbedding.exists_actual_scalarCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_matrixCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_fixedChartDensity_scalarCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_fixedChartDensity_matrixCoefficient_principal_energy_bound`

[共同源码对应](a01-principal-energy-source-bindings.json)
