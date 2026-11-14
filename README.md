# Burnett-conjecture

这是论文 **High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture** 的 Lean 工程。远程仓库为 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture)，已通过 GitHub API 确认可见性为**私有**。构建运行见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions)，固定提交和实际运行状态由 GitHub 记录。

当前状态为 `development`：首个实数非特征 Ricci 符号代数片段已有 **5条 Lean 支持定理**。原文17项正式 theorem/lemma/proposition/corollary 仍均未完成；已有支持引理不计作其中一项完成。关键未编号断言、必要定义和依赖的完整覆盖仍待核对，整篇数学与输运主线尚未闭合。

原文快照为 [`paper/burnett.tex`](paper/burnett.tex)，176424字节，SHA256：

```text
e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e
```

来源身份见 [`paper/source.json`](paper/source.json)。该副本保留用户原文件字节；Git 对该文件禁用行尾转换。

工程固定 **Lean 4.24.0** 和 **Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**，其余依赖见 `lake-manifest.json`。该选择已由近期代数接口实际探针验证；中期测度、微局部分析与几何接口仍有待补的桥接和实现。

```powershell
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python scripts/check_project.py --repo .
```

本机可用已存在的SDK：

```powershell
$env:PATH = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin;' + $env:PATH
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python scripts/check_project.py --repo . --lake 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe'
```

此 PATH 设置只影响当前终端，确保缓存程序内部再调用 `lake` 时也使用同一SDK。

入口核对原文身份、标准、固定运行时并构建库入口；对当前5个真实支持目标再调用 `scripts/check_paper.py` 做存在性、来源和传递公理审计。机器通过仍不能代替结果覆盖、语义对应或作者确认，`paper_formalization_verified` 保持false。没有目标的初始阶段仅输出 `project-setup-passed`。

- [`RicciSymbol.lean`](Burnett/Algebra/RicciSymbol.lean) 实现实数非特征核的显式规范表示和二次消去；[数学解释及实际声明](docs/statements/ricci-symbol.md)、[独立回读](docs/statements/ricci-symbol-review.md)。
- [`主定理接口`](docs/statements/main-interface.md)、[`主线依赖`](docs/formalization/dependencies.md)、[`库调查`](docs/formalization/library-audit.md) 记录当前对象、量词、消费者和实际库证据。
- [`docs/statements/`](docs/statements/) 保存原文结果索引与未来数学/Lean对照。
- [`docs/formalization/scope.json`](docs/formalization/scope.json) 是范围与进度的主清单；完整二次代数父项仍为部分完成。
- [`docs/formalization/review.md`](docs/formalization/review.md) 记录实际复核及发布情况。
- [`docs/formalization/standard.zh-CN.md`](docs/formalization/standard.zh-CN.md) 固定 `paper-results` 第1.2版标准。
- [`tools/lean-paper-results/`](tools/lean-paper-results/) 是该技能的文本快照；维护负例套件无需逐篇论文重复运行。

最终信任政策仍在项目记录中单列。当前机器检查使用标准三基础公理配置；不把它推定为其他项目的政策。当前片段的最终机器、独立复核、作者确认和CI状态见复核记录。后续沿完整二次展开、极化及零锥规范商正性继续推进，并补核输运所需外部精确定理。
