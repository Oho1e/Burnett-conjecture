# 形式化复核与工程状态

## 原文与标准

原文快照 `paper/burnett.tex`，176424字节，SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`；用户原件保持不动。采用 `paper-results` 第1.2版，标准SHA256 `8caad6c9439a86c17567c84bcc065c24a44e11830657ff9996bb13f259cae2f0`。原文是 proposed proof；工程进度不构成整篇正确性结论。

## 当前数学进展

2026-11-15：已完成[主定理精确接口](../statements/main-interface.md)、[关键依赖与消费者](dependencies.md)及[固定库调查](library-audit.md)。11项主线接口仅核对原文对象、使用位置、常数与极限顺序，未证明其中的分析结论；5项精确外部引用仍待原文核实。

首个实际Lean模块为 `Burnett.Algebra.RicciSymbol`，源码SHA256 `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`。5条支持定理实现实数非特征Ricci核的显式纯规范表示、升指标/连接主符号展开及实对角二次消去。数学解释与逐字声明见[ricci-symbol.md](../statements/ricci-symbol.md)。

项目状态仍为 `development`。原文17项正式结果均未完成；`unnum:quadratic-symbol-algebra` 整项保持部分完成。完整二次展开、混合/Hermitian极化、零锥与商空间非负性，以及测度、输运、全局提升和主定理都尚未闭合。

## 机器与语义证据

实现者和独立复核者分别用核实固定版本的只读库路径直接编译实际源码/自有探针，均退出0；5条定理的实际传递公理集仅为 `propext`、`Classical.choice`、`Quot.sound`，无sorryAx、新增数学公理或native_decide。

独立代理先从实际代码和类型写出数学含义，再读原文比较，局部语义核对通过；详细范围、一般实系数与真实逆Lorentz分量的适用关系、探针路径和未覆盖项见[独立回读](../statements/ricci-symbol-review.md)。上述只读探针不替代本项目独立Lake构建或真实CI。

本项目已固定Lean4.24.0与Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`，另8包固定于manifest。依赖源经独立Git对象/工作树检出，official origin与固定rev核对；没有复制父工程构建缓存或修改共享源。官方定向缓存917文件已实际取得并解压。项目自身固定环境已完成根入口构建、5个目标的存在性/来源与传递公理审计，实际退出0；独立复核者也在本项目依赖路径上重编译最终源码，退出0，类型和公理输出一致。机器记录见 `.project-verification/` 与 `.paper-verification/`；最终提交前再次刷新绑定。

用户/作者对本片段普通数学解释的确认：已提交具体问题，等待实际答复。最终信任政策沿用scope当前待决记录；实际三公理报告本身不冒充政策批准。临时数学条件接口：当前片段没有；其他尚未实现的主线接口保持开放。

## 远程与历史记录

仓库 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture) 已实际创建并通过API核实为私有。此前[首次初始化CI记录](remote-evidence.json)仍是对应旧源码提交的有效历史，检查时没有论文目标。

本轮证明与依赖变更推送后的固定提交和CI须另按实际记录；旧初始化绿色不移用为新片段已通过。本工程未发布整篇已验证标签。
