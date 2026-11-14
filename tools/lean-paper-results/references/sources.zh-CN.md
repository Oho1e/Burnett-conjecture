# 本标准的调研依据

本文件保存 2026-11-14 上一轮实际调研得到的设计依据，不把期刊政策或个人意见当成跨期刊统一认证规则。使用于未来投稿时，目标期刊的具体政策仍应重新核查。

## 期刊规范

以下可访问的官方指南没有列明 Lean/证明助手或逐段形式化覆盖率要求；这是所查页面的结论，不是穷尽所有编辑规则的证明。

- [Communications in Mathematical Physics](https://link.springer.com/journal/220/submission-guidelines)
- [Annales Henri Poincaré](https://link.springer.com/journal/23/submission-guidelines)
- [Letters in Mathematical Physics](https://link.springer.com/journal/11005/submission-guidelines)
- [Archive for Rational Mechanics and Analysis](https://link.springer.com/journal/205/submission-guidelines)
- [Journal of Mathematical Physics 编辑政策](https://pubs.aip.org/aip/jmp/pages/policies)
- [Journal of Physics A](https://publishingsupport.iopscience.iop.org/journals/journal-of-physics-a-mathematical-and-theoretical/)
- [Classical and Quantum Gravity](https://publishingsupport.iopscience.iop.org/journals/classical-and-quantum-gravity/)
- [Nonlinearity](https://publishingsupport.iopscience.iop.org/journals/nonlinearity/)

数据与代码可用性条款不能推导强制数学形式化。IOP 的补充材料说明还区分了随稿材料与默认同行评审范围：不能把普通期刊录用写成期刊独立认证了形式化代码。

专门的 [AFM 作者指南](https://afm.episciences.org/page/instructions-for-authors) 要求形式化 artifact、自然语言与形式声明对应，以及至少主结果链接到具体代码；[AFM 宗旨](https://afm.episciences.org/page/aims-and-scope) 将通用性、库整合等列为值得追求但非每项必需的优点。这不等于自动接受任意主结果附件，也不等于默认要求 mathlib 投稿质量。

## 社区核验与实践

- [Lean 社区 Did you prove it?](https://leanprover-community.github.io/did_you_prove_it.html)：版本化项目、实际构建、公理依赖及所证命题确实对应所声称的结果。
- [mathlib-initiative 的 formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)：报告范围、差异、依赖和审阅状态的自述格式，本身不是认证。
- [PFR 项目范围记录](https://github.com/teorth/pfr/blob/master/formalization.yaml)：公开区分具体完成目标及未形式化推论，说明范围必须明确。本轮调研读了项目声明，没有重新构建项目。
- [2023 年原研究与形式化合并投稿讨论](https://leanprover-community.github.io/archive/stream/113488-general/topic/merging.20formalization.20into.20the.20original.20paper.html)：Thomas Bloom、Eric Wieser 等分享投稿经历；属于具名个人经验，不是期刊统一政策。

据此提出本标准：覆盖全部正式数学结果及必要依赖，准确说明对象、假设、结果和版本；不默认把每处无关旁述、所有例子及原文每条证明路线扩成形式化目标。此建议作为独立标准保存，不撤销其他更严格或更局部的标准。
