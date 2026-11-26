# Source index and statement entry points

[简体中文](README.md)

The status below belongs to the initial inventory. [Current scope](../formalization/scope.json) · [Review history](../formalization/review.en.md)

Locked source: `paper/burnett.tex`, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. Line numbers are one-based positions in that source file, not PDF page numbers.

The initial index identifies 17 formal result environments (3 theorems, 6 lemmas, 6 propositions, and 2 corollaries), together with 33 candidate unnumbered results and 15 candidate definitions. Real noncharacteristic elimination, the full real B expansion, the real null-cone kernel/B formula, and real gauge cross terms have been implemented. General polarization, complex Hermitian results, and quotient positivity remain open; the 17 formal results remain unfinished, and their dependencies are only partially formalized. Candidate scope and the necessary dependency closure remain under review. Environment numbers are inferred from the TeX counters and have not been checked against a compiled PDF.

- [Source statements and future Lean correspondence](main.en.md)
- [Complete machine-readable index](source-index.json)
- [Initial structural inventory and candidate notes](intake.en.md)
- [Precise interface for the main theorem](main-interface.en.md)
- [Angular Fourier commutators and fixed low-frequency regularization](angular-cutoff-commutator.en.md)
- [Positive matrix-measure representation](positive-matrix-measure.en.md)
- [First Ricci-symbol fragment](ricci-symbol.en.md) and [independent readback of its actual declarations](ricci-symbol-review.en.md)
- [Strong local H⁻¹ convergence of linearized Ricci](geometric-Hminus-closure.en.md) and [independent review](geometric-Hminus-closure-review.en.md)
- [Intrinsic curvature, the Ricci trace, and chartwise vacuum](intrinsic-curvature-Ricci.en.md) and [independent review](intrinsic-curvature-Ricci-review.en.md)
- [Finite-dimensional variation and Ward identities](transport-ward.en.md) and [review](transport-ward-review.en.md)
- [Multiscale Rosen vacuum sequence](rosen-multiscale.en.md) and [mathematical review](rosen-multiscale-review.en.md)
- [General two-polarization Rosen proposition](rosen-two-polarization.en.md) and [mathematical review](rosen-two-polarization-review.en.md)
- [Local weighted disintegration and base-measure tests](local-disintegration.en.md)
- [Countable-cover disintegration for a fixed joint measure](countable-fiber-disintegration.en.md)
- [F05 geometry on preferred chart overlaps](chart-overlap-geometry.en.md)
- [Changing the auxiliary metric in the vacuum sequence hypotheses](auxiliary-metric-admissibility.en.md)
- [Fourier symbols for the cubic-energy commutator](cubic-energy-fourier-symbols.en.md)
- [Maximal and annular square estimates in four dimensions](harmonic-maximal-and-square-estimates.en.md)
- [Angular kernel transforms](angular-kernel-transforms.en.md)
- [Shifted Fourier window estimates in four dimensions](shifted-fourier-window-estimates.en.md)
- [Compact Fourier multipliers between spatial cutoffs](compact-frequency-localization.en.md)
- [Signed Fourier windows in four dimensions](signed-fourier-window-estimates.en.md)
- [Four-dimensional annular square and product estimates](annular-square-and-product-estimates.en.md)
- [Quantitative joint Fourier multiplier estimates](joint-fourier-multiplier-estimates.en.md)
- [F05 first-order localization and the original curl](bessel-and-coordinate-curl.en.md)
- [Actual bilinear and scalar Fourier multipliers](bilinear-fourier-operators.en.md)
- [Complete cubic energy in the Lean library](complete-cubic-energy.en.md)
- [Frozen screen and phase identity](frozen-screen.en.md)
- [Principal-energy commutator estimates](a01-principal-energy.en.md)
- Scope and progress are maintained only in `../formalization/scope.json`; this directory retains source references and correspondence material.

| Expected source number | Kind | Label | Source lines | Lean status |
| --- | --- | --- | --- | --- |
| 1.1 | theorem | `thm:main` | 139–168 | Not modeled |
| 2.1 | theorem | `thm:quadratic` | 354–356 | Not modeled |
| 2.2 | corollary | `cor:base-marginal` | 487–506 | [Proof implemented](base-marginal-and-angular-disintegration.en.md) |
| 3.1 | lemma | `lem:commutator` | 566–575 | Not modeled |
| 3.2 | lemma | `lem:cubic-continuity` | 613–623 | [Proof implemented](paper-cubic-continuity.en.md) |
| 3.3 | lemma | `lem:freezing` | 736–764 | Not modeled |
| 3.4 | lemma | `lem:analytic-near` | 1026–1057 | Not modeled |
| 3.5 | lemma | `lem:analytic-correction-bounds` | 1380–1394 | [High-slot commutators and the exact physical far symbol](high-slot-and-physical-far-symbol.en.md) · [Original angular correction and cutoff recovery](original-angular-cutoff-recovery.en.md) |
| 4.1 | proposition | `prop:general-projection` | 1600–1616 | [Projected source in arbitrary charts](original-general-projection.en.md) |
| 5.1 | theorem | `thm:variational-transport` | 1729–1735 | Not modeled · [Assembly of the original gauge and far corrections](original-correction-assembly.en.md) |
| 6.1 | lemma | `lem:lift` | 2989–2991 | [Full momentum from a smooth spacelike Cauchy slice](cauchy-momentum-lift.en.md) · [Globally hyperbolic full momentum lift](globally-hyperbolic-momentum-lift.en.md) |
| 6.2 | corollary | `cor:strong` | 3063–3078 | [Strong compactness on vacuum regions](strong-compactness.en.md) |
| A.1 | proposition | `prop:shear` | 3121–3123 | [Proof and independent review](harmonic-shear.en.md) |
| B.1 | proposition | `prop:cubic` | 3175–3181 | Not modeled |
| C.1 | proposition | `prop:bianchi` | 3245–3247 | [Proof and independent review](bianchi-counterexample.en.md) |
| D.1 | proposition | `prop:rosen` | 3307–3312 | [Proof and independent review](rosen-two-polarization.en.md) |
| D.2 | proposition | `prop:flat-rigidity` | 3390–3392 | [Proof and independent review](flat-rigidity.en.md) |
- [Angular caps and the signed phase gap](angular-cap-geometry.en.md)
- [Fixed gauge-complement projection and its order-zero symbol](fixed-gauge-projection.en.md)
- [Fourier action of the fixed gauge-complement projection](gauge-projection-fourier-action.en.md)
- [Finite-exponent norms of the fixed projected fields](projected-field-finite-lp.en.md)
- [Uniform smallness of the fixed projected fields](projected-field-uniform-convergence.en.md)
- [Norms of the projected fields from the original open chart](open-chart-projected-norms.en.md)
- [Derivative commutator for the fixed infrared factor](projection-infrared-commutator.en.md)
- [Derivative commutator for the fixed matrix projection](projection-hodge-commutator.en.md)
- [Projected vacuum remainder and whole-space divergence source](projected-vacuum-source.en.md)
- [Uniform projected divergence source in any smooth chart](maximal-chart-projected-source.en.md)
- [Angular covariance and physical measure of the fixed projection](projected-angular-covariance.en.md)
- [Weighted mixed derivative pairings of the actual projected field](weighted-projected-derivative-pairings.en.md)
- [Local positive matrix measures for the original metric gradients](original-gradient-matrix-measures.en.md)
- [Curl factorization and projected pairings of the original metric gradients](original-volume-curl-amplitudes.en.md)
- [Vacuum Ricci kernel and auxiliary unit cosphere amplitudes](original-volume-ricci-amplitudes.en.md)
- [Gradient transformation and Fourier comparison on preferred-chart overlaps](overlap-fourier-conjugation.en.md)
- [Angular test pairings after a change of charts](moving-angular-density-pairings.en.md)
- [Overlap matrix measures with matching transported cutoffs](matching-cutoff-matrix-measures.en.md)
- [Overlap matrix measures for independently chosen cutoffs](independent-cutoff-matrix-measures.en.md)
- [Positive physical measures on original charts](local-positive-physical-measures.en.md)

- [Global physical measure and chart Ricci moments](global-physical-ricci-moments.en.md)

- [Global Einstein moments and change of auxiliary unit section](global-cosphere-einstein-moments.en.md)

- [Global intrinsic amplitude covariance and the original physical measure](global-intrinsic-amplitude-covariance.en.md)

- [Represent the original jet covariance in arbitrary receiving charts](receiving-chart-jet-covariance.en.md)

- [Localize the original covariant jets and assemble their intrinsic measure](symmetric-jet-localization.en.md)

- [Transport joint classical symbols and disintegrate the original physical measure](joint-classical-tests-and-base-marginal.en.md)
- [Weighted change of auxiliary unit section](weighted-auxiliary-section-change.en.md)
- [Positive null second moments](quadratic-null-second-moments.en.md)
- [Original projected patch sources and wide frozen errors](original-transport-patch-estimates.en.md)
- [Frozen cubic action, thin-screen replacement, and the physical far symbol](frozen-cubic-transport.en.md)
- [All-scale and adjacent-cap trilinear estimates](all-scale-transfer.en.md)
