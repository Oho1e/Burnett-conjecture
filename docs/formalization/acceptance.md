# 论文结果验收记录

[English](acceptance.en.md)

锁定论文的 17 个编号结果和 3 个已批准的未编号结果已按项目采用的 paper-results 1.2 完成形式化。20 项的原文位置、Lean 声明、传递公理和所用复核报告均列在同一份验收清单。范围包含这些结果所需的定义和证明依赖。附录三则说明例（原文 3430–3445 行）列在原文索引中。 [验收清单](acceptance.json) · [项目范围](scope.json) · [原文索引](../statements/source-index.json)

## 语义验收

协调者和三位独立复核者从实际 Lean 类型、重要定义及其证明回读原文含义。项目用户于 2026 年 11 月 28 日报告人类语义审查通过，确认范围为复核材料中的 20 项及其解释。清单记录该材料、类型探针、日志及各份复核报告的哈希。此前对三线性反例的委托确认也保存在对应条目的历史字段。

三次冻结引理采用局部经典振幅与弱配对表示，并使用固定红外正则化的冻结算子。三次连续性和解析修正的非齐次结论采用固定有界频率正则化。主定理沿同一原序列的一条子列、同一协方差及其物理测度建立 Einstein 矩、Hamilton 输运和全局双曲开区上的全动量提升。 [三次冻结](../statements/original-cubic-freezing.zh-CN.md) · [正向动理学极限](../statements/original-forward-kinetic-limit.zh-CN.md)

必要依赖复核追踪了附录恒等式在弱 Ricci、强 H⁻¹ 收敛及二次加权换截面中的实际用法。交换子引理的标量和 Hermitian 系数入口均登记在验收清单中。 [弱 Ricci](../statements/weak-ricci-identification.md) · [局部强 H⁻¹](../statements/geometric-Hminus-closure.md) · [加权换截面](../statements/weighted-auxiliary-section-change.zh-CN.md)

## 固定版本与复验

| 项目 | 版本 |
| --- | --- |
| 受审证明提交 | [208064b36a5fa971ddad2f2f0e946c512d3c44c4](https://github.com/Oho1e/Burnett-conjecture/commit/208064b36a5fa971ddad2f2f0e946c512d3c44c4) |
| 受审 Git 树 | `5385d6090630f226d63550807d8a4990aa1301b1` |
| 论文 SHA256 | `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| Lean | [4.24.0](../../lean-toolchain) |
| mathlib | [f897ebcf72cd16f89ab4577d0c826cd14afaafc7](../../lake-manifest.json) |

按 README 准备锁定工具链与依赖后，从仓库根目录运行以下命令。GitHub Actions 同时记录候选合并提交及实际主线提交各自的回执。 [复现说明](../../README.zh-CN.md) · [检查流程](../../.github/workflows/project-check.yml)

```sh
python scripts/check_slices.py --repo .
python scripts/test_slices.py
python scripts/check_project.py --repo . --timeout 7200 --build-timeout 14400
```

受审证明提交的主线运行检查了 1,157 个登记目标及其传递公理。依赖检查核对了 2,212 份 Lean 源码。信任政策 A 允许 `propext`、`Classical.choice` 和 `Quot.sound`。机器检查返回 `machine-check-passed`。项目验收结论由范围清单登记，并与该机器回执和人类语义确认绑定。 [主线运行与工件](https://github.com/Oho1e/Burnett-conjecture/actions/runs/46115144766) · [验收清单](acceptance.json)
