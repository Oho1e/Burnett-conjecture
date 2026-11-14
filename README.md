# Burnett-conjecture

这是论文 **High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture** 的 Lean 工程。远程仓库为 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture)，已通过 GitHub API 确认可见性为**私有**。构建运行见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions)，固定提交和实际运行状态由 GitHub 记录。

当前只建立工程和原文索引：`development`，**0 个 Lean 论文目标、0 个已完成论文结果**。原文中的正式 theorem/lemma/proposition/corollary 共17项已建立来源索引；关键未编号断言、必要定义和依赖的覆盖仍待独立核对。没有进行整篇证明、正确性审稿、反向语义核验或作者确认。

原文快照为 [`paper/burnett.tex`](paper/burnett.tex)，176424字节，SHA256：

```text
e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e
```

来源身份见 [`paper/source.json`](paper/source.json)。该副本保留用户原文件字节；Git 对该文件禁用行尾转换。

工程固定 **Lean 4.24.0**，当前无外部依赖。**Mathlib尚未选择兼容版本**；后续按实际建模需要锁定，不能把当前空依赖启动配置解释为所需数学库已经准备完毕。

```powershell
lake build
python scripts/check_project.py --repo .
```

本机可用已存在的SDK：

```powershell
python scripts/check_project.py --repo . --lake 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe'
```

无论文目标时，入口核对原文身份、标准与工程配置并实际构建，只输出 `project-setup-passed`，同时保持 `paper_formalization_verified: false`。有真实目标登记后，入口调用 `scripts/check_paper.py` 做目标构建与传递公理审计；该机器检查仍不能代替结果覆盖、语义对应或作者确认。CI采用同一阶段入口，初始化绿色不表示论文已经形式化。

- [`Burnett.lean`](Burnett.lean) 导入命名空间目录；当前只有文档入口。
- [`docs/statements/`](docs/statements/) 保存原文结果索引与未来数学/Lean对照。
- [`docs/formalization/scope.json`](docs/formalization/scope.json) 是范围与进度的主清单，当前 `targets: []`。
- [`docs/formalization/review.md`](docs/formalization/review.md) 记录实际复核及发布情况。
- [`docs/formalization/standard.zh-CN.md`](docs/formalization/standard.zh-CN.md) 固定 `paper-results` 第1.2版标准。
- [`tools/lean-paper-results/`](tools/lean-paper-results/) 是该技能的文本快照；维护负例套件无需逐篇论文重复运行。

最终信任政策待用户决定。当前工具仅提供标准三基础公理配置；本轮没有将其写成用户已批准的最终政策。下一步应核对未编号范围与必要定义，再选取适中的重要结果开始数学陈述和Lean建模。
