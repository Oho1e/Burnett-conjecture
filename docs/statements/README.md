# 原文索引与陈述入口

[English](README.en.md)

下文保留初始清点时的状态。当前进度见[范围清单](../formalization/scope.json)与[复核记录](../formalization/review.md)。

锁定原文：`paper/burnett.tex`，SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。行号为该源文件的1起算行号，不是PDF页码。

初始索引定位17个正式结果环境（3 theorem、6 lemma、6 proposition、2 corollary），并登记33项未编号结果候选、15项定义候选。现已实现实非特征消去、完整实B展开、实零锥核/B公式及实规范交叉；一般极化、复Hermitian与商正性仍开放；17项正式结果仍待完成，父依赖仍仅部分形式化。候选范围及必要依赖闭包继续核对。环境编号按TeX计数器推得，尚未经编译PDF核验。

- [逐项原文陈述与未来Lean对照](main.md)
- [机器可读完整索引](source-index.json)
- [初始结构清点及候选说明](intake.zh-CN.md)
- [主定理的精确接口](main-interface.md)
- [首个 Ricci 符号片段](ricci-symbol.md)及[独立实际声明回读](ricci-symbol-review.md)
- [多尺度 Rosen 真空序列](rosen-multiscale.md)及[数学复核](rosen-multiscale-review.md)
- 主范围及进度仅在 `../formalization/scope.json` 维护；本目录保留来源与对应材料。

| 原文预计编号 | 类型 | 标签 | 源码行 | Lean状态 |
| --- | --- | --- | --- | --- |
| 1.1 | theorem | `thm:main` | 139–168 | 未建模 |
| 2.1 | theorem | `thm:quadratic` | 354–356 | 未建模 |
| 2.2 | corollary | `cor:base-marginal` | 487–506 | 未建模 |
| 3.1 | lemma | `lem:commutator` | 566–575 | 未建模 |
| 3.2 | lemma | `lem:cubic-continuity` | 613–623 | 未建模 |
| 3.3 | lemma | `lem:freezing` | 736–764 | 未建模 |
| 3.4 | lemma | `lem:analytic-near` | 1026–1057 | 未建模 |
| 3.5 | lemma | `lem:analytic-correction-bounds` | 1380–1394 | 未建模 |
| 4.1 | proposition | `prop:general-projection` | 1600–1616 | 未建模 |
| 5.1 | theorem | `thm:variational-transport` | 1729–1735 | 未建模 |
| 6.1 | lemma | `lem:lift` | 2989–2991 | 未建模 |
| 6.2 | corollary | `cor:strong` | 3063–3078 | 未建模 |
| A.1 | proposition | `prop:shear` | 3121–3123 | 未建模 |
| B.1 | proposition | `prop:cubic` | 3175–3181 | 未建模 |
| C.1 | proposition | `prop:bianchi` | 3245–3247 | 未建模 |
| D.1 | proposition | `prop:rosen` | 3307–3312 | 未建模 |
| D.2 | proposition | `prop:flat-rigidity` | 3390–3392 | 未建模 |
