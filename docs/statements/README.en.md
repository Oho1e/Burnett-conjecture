# Source index and statement entry points

[简体中文](README.md)

The status below belongs to the initial inventory. [Current scope](../formalization/scope.json) · [Review history](../formalization/review.en.md)

Locked source: `paper/burnett.tex`, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. Line numbers are one-based positions in that source file, not PDF page numbers.

The initial index identifies 17 formal result environments (3 theorems, 6 lemmas, 6 propositions, and 2 corollaries), together with 33 candidate unnumbered results and 15 candidate definitions. Real noncharacteristic elimination, the full real B expansion, the real null-cone kernel/B formula, and real gauge cross terms have been implemented. General polarization, complex Hermitian results, and quotient positivity remain open; the 17 formal results remain unfinished, and their dependencies are only partially formalized. Candidate scope and the necessary dependency closure remain under review. Environment numbers are inferred from the TeX counters and have not been checked against a compiled PDF.

- [Source statements and future Lean correspondence](main.en.md)
- [Complete machine-readable index](source-index.json)
- [Initial structural inventory and candidate notes](intake.en.md)
- [Precise interface for the main theorem](main-interface.en.md)
- [First Ricci-symbol fragment](ricci-symbol.en.md) and [independent readback of its actual declarations](ricci-symbol-review.en.md)
- [Intrinsic curvature, the Ricci trace, and chartwise vacuum](intrinsic-curvature-Ricci.en.md) and [independent review](intrinsic-curvature-Ricci-review.en.md)
- Scope and progress are maintained only in `../formalization/scope.json`; this directory retains source references and correspondence material.

| Expected source number | Kind | Label | Source lines | Lean status |
| --- | --- | --- | --- | --- |
| 1.1 | theorem | `thm:main` | 139–168 | Not modeled |
| 2.1 | theorem | `thm:quadratic` | 354–356 | Not modeled |
| 2.2 | corollary | `cor:base-marginal` | 487–506 | Not modeled |
| 3.1 | lemma | `lem:commutator` | 566–575 | Not modeled |
| 3.2 | lemma | `lem:cubic-continuity` | 613–623 | Not modeled |
| 3.3 | lemma | `lem:freezing` | 736–764 | Not modeled |
| 3.4 | lemma | `lem:analytic-near` | 1026–1057 | Not modeled |
| 3.5 | lemma | `lem:analytic-correction-bounds` | 1380–1394 | Not modeled |
| 4.1 | proposition | `prop:general-projection` | 1600–1616 | Not modeled |
| 5.1 | theorem | `thm:variational-transport` | 1729–1735 | Not modeled |
| 6.1 | lemma | `lem:lift` | 2989–2991 | Not modeled |
| 6.2 | corollary | `cor:strong` | 3063–3078 | Not modeled |
| A.1 | proposition | `prop:shear` | 3121–3123 | Not modeled |
| B.1 | proposition | `prop:cubic` | 3175–3181 | Not modeled |
| C.1 | proposition | `prop:bianchi` | 3245–3247 | Not modeled |
| D.1 | proposition | `prop:rosen` | 3307–3312 | Not modeled |
| D.2 | proposition | `prop:flat-rigidity` | 3390–3392 | Not modeled |
