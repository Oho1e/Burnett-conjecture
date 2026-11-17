# Initial structural inventory of the Burnett article

Project copy: the original machine-specific path is replaced by project-relative `paper/burnett.tex`; source hash, locations, and status otherwise remain unchanged.

This pass initializes a new project. Every mathematical claim retains the source's **proposed proof** status: **not yet modeled/formalized, without a mathematical truth/correctness review or an independent Lean-statement correspondence review**. This inventory neither proves nor repairs article mathematics.

## Locked source

- Source: `paper/burnett.tex`.
- SHA-256：`e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。
- Original size176,424 bytes; UTF-8, LF;3475 lines. References below are one-based inclusive lines of that hashed source.
- Title: *High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture*. Author/date fields are empty.
- All source lines1–3475 were read with the original unchanged. TeX sections/environments/labels were extracted and narrative candidates added by paragraph reading; no LaTeX compilation was run.

## Mathematical topics and boundaries

The source treats high-frequency vacuum-metric limits on smooth four-dimensional spacetimes: locally uniform metric convergence to a smooth time-oriented Lorentz limit, locally uniform first-derivative bounds, without coordinate conditions, symmetry, or a scale relating second derivatives to amplitudes. The main claim proposes Einstein second moments and Hamiltonian transport for the same nonnegative null-ray measure; full-momentum measures with locally finite second moments are additionally obtained on globally hyperbolic open subspacetimes.

Quadratic positivity/null moments are explicitly distinguished from transport. Complete cubic variation and vanishing of its transport residual are central proposed-proof claims. Reverse approximation, nonsmooth limits, concentrations beyond the stated first-derivative bounds, nonzero cosmological constant, and other dimensions lie outside this intake (178–190).

Topics for later module planning: basic geometry/admissible sequences; finite-dimensional Ricci-symbol/gauge-quotient algebra; tensor defects/positive measures; Fourier/PDO/trilinear estimates; bounded scalar sources for physical projections; action variations/Ward identities/two corrections; variable-background localization/ordered limits; globally hyperbolic lifts; appendix examples/identities. This is navigation only: no Lean definitions, library interfaces, or first proof task have been chosen.

## Sections and appendices

| Number | Source title | Label | Source lines |
|---|---|---|---|
| 1 | Introduction | `sec:introduction` | 86–351 |
| 2 | Preliminaries | `sec:quadratic` | 352–518 |
| 3 | Analytic estimates for cubic energies | `sec:analytic` | 519–1591 |
| 4 | A bounded physical source in arbitrary coordinates | `sec:general-projection` | 1592–1719 |
| 5 | The variational transport identity and cubic cancellation | `sec:variational-transport` | 1720–2642 |
| 6 | Proof of Theorem~\ref{thm:main} | `sec:completion` | 2643–3115 |
| A | A harmonic-coordinate example with an unbounded source | `sec:shear` | 3116–3172 |
| B | Characteristic localization and cubic interactions | `sec:cubic` | 3173–3212 |
| C | Conservation and positive null moments do not give transport | `sec:rotating` | 3213–3304 |
| D | The Rosen plane-wave class | `sec:rosen` | 3305–3424 |
| E | Auxiliary identities and coordinate oscillations | None | 3425–3463 |

Body:86–3113; `\appendix`:3115; appendicesA–E:3116–3463; references:3464–3474. AppendixE has no source section label. Exact subsection/five-paragraph ranges are in `source-index.json` under `headings`.

## Initial formal-result index

Numbers follow the shared theorem-counter rules, without compiled-PDF checking. Every row means proposed in source, not modeled/formalized. Statement lines locate only result environments; JSON separately locates proof environments/adjacent narrative arguments, without certifying their content/coverage.

| Expected number | Kind | Source label | Source title | Statement lines |
|---|---|---|---|---|
| 1.1 | theorem | `thm:main` | Forward kinetic limit in the smooth-limit class | 139–168 |
| 2.1 | theorem | `thm:quadratic` | Positive null second moments, without transport | 354–356 |
| 2.2 | corollary | `cor:base-marginal` | Base marginal and angular disintegration | 487–506 |
| 3.1 | lemma | `lem:commutator` | Lipschitz-small coefficients in a symmetric energy pairing | 566–575 |
| 3.2 | lemma | `lem:cubic-continuity` | Continuity of the complete cubic energy | 613–623 |
| 3.3 | lemma | `lem:freezing` | Quantitative freezing of a complete cubic energy | 736–764 |
| 3.4 | lemma | `lem:analytic-near` | All-scale transfer and angular summation | 1026–1057 |
| 3.5 | lemma | `lem:analytic-correction-bounds` | Bounds for the correction and its rough commutator | 1380–1394 |
| 4.1 | proposition | `prop:general-projection` | A projected source without a coordinate condition | 1600–1616 |
| 5.1 | theorem | `thm:variational-transport` | Transport under the original first-derivative hypotheses | 1729–1735 |
| 6.1 | lemma | `lem:lift` | Local-moment version of the globally hyperbolic lift | 2989–2991 |
| 6.2 | corollary | `cor:strong` | Vacuum limits and strong physical compactness | 3063–3078 |
| A.1 | proposition | `prop:shear` | Failure of a background $L^2$ source estimate | 3121–3123 |
| B.1 | proposition | `prop:cubic` | An auxiliary trilinear counterexample | 3175–3181 |
| C.1 | proposition | `prop:bianchi` | Geometric nonrepresentability without vacuum approximation | 3245–3247 |
| D.1 | proposition | `prop:rosen` | Two-polarization Rosen closure | 3307–3312 |
| D.2 | proposition | `prop:flat-rigidity` | Flat admissible sequences have flat smooth limits | 3390–3392 |

There are17 explicit formal result environments:3 theorem,6 lemma,6 proposition,2 corollary. Two remarks at170–176 and178–190 share the counter, expected as1.2/1.3; no explicit definition/problem instance exists. There are16 proof environments; `thm:quadratic` is argued in adjacent prose358–485 without a separate proof environment. This records source structure, not proof completeness or formalization coverage.

Source-stated relationships: the main result combines `thm:quadratic`, `thm:variational-transport`, `lem:lift` (3046–3061); `lem:lift` assumes transport (2989–3043); arguments for `cor:base-marginal`/`cor:strong` say they do not use transport (507–517,3079–3113). JSON references reflect occurrences in source, not an independently verified dependency graph.

## Candidate unnumbered results

Many algebraic facts, estimates, constructions, and examples occur in prose. These33 are initial candidates to decide individually during modeling, not accepted Lean targets or an exhaustive list of implicit claims/assumptions/obligations.

| Candidate topic | Source lines |
|---|---|
| Local H^{-1} compactness/strong vanishing of linearized Ricci | 360–388 |
| Common microlocal defect measure, one subsequence, Ricci-kernel constraints | 392–428 |
| Full quadratic algebra, pure-gauge elimination off the cone, null-quotient positivity | 432–465 |
| Physical measure construction and weighted change under auxiliary-metric replacement | 469–485 |
| Smooth-coefficient difference bounds for cubic energy | 719–734 |
| Low/high and comparable triple partitions, adjacent-cap geometry | 895–951 |
| Finite-exponent cap-multiplier bounds and angular-index L^3 summation | 953–992 |
| Exact scalar phase gap in separated physical directions | 994–1016 |
| Independent low-angular-variable expansion, BS^1 symbols, finite derivative thresholds | 1248–1377 |
| Quartic commutator bounds for divergence operators and corrections | 1476–1504 |
| Exact correction-operator identities and bounded-source pairings | 1506–1526 |
| Removal of finite angular sums/upper-frequency truncations at fixed n | 1528–1590 |
| Exact Hermitian principal symbol of the density Hessian and gauge compression | 1747–1809 |
| Hessian commutators, nonlinear remainder pairings, complete cubic transport residual | 1811–1904 |
| Lower-order complete-cubic variation, cyclic Fourier vertices, polarization continuity | 1906–2009 |
| Explicit frozen-screen projection matrices and physical-phase extraction | 2053–2107 |
| Off-shell Ward identity and classification by one/two/three gauge factors | 2109–2261 |
| Low-gauge correction, Hermitian symmetry, independent-variable extension | 2265–2341 |
| Quadratic angular test-symbol gain and operator bounds for complete near-cap physical interactions | 2343–2502 |
| Exact phase division/extension for physical far-cap low/high interactions | 2504–2555 |
| Pairing bounds for both corrections and original projected-field scalar wave equations | 2557–2590 |
| Exact near-cap/correction/physical-phase assembly of the complete frozen cubic term | 2592–2641 |
| Cubic localization and quantitative freezing with variable backgrounds | 2647–2729 |
| Defect-measure expression of whole-space projected-gradient norms | 2731–2758 |
| Frozen-screen/phase errors and finite-exponent interpolation | 2760–2841 |
| Patch summation, final residual bound, ordered limits | 2843–2985 |
| Rotating positive null-moment tensor on flat background: conservation does not imply transport | 3215–3239 |
| Explicit multiscale Rosen vacuum sequences and exact zero-source coordinates | 3360–3386 |
| Multiscale flat-pullback example | 3430–3439 |
| Spacelike raw-gradient defect with zero physical measure | 3441–3442 |
| Weak-energy-type algebraic properties insufficient for positive real covector second moments | 3444–3445 |
| Distributional/H^{-1} identity for products of second derivatives | 3447–3459 |
| Two-homogeneous test weights under unit-section change | 3461–3462 |

The rotating-moment example opening AppendixC has no proposition environment (3215–3239); the explicit multiscale Rosen example in AppendixD also has no standalone result environment (3360–3386). All five AppendixE paragraphs are separate candidates. Auxiliary counterexamples inA/B/C retain their original limitations, not registered as counterexamples to the main theorem.

## Candidate definitions and notation

Although no explicit definition environment appears, prose defines these modeling objects. Their Lean types, contexts, conventions, and source correspondence remain to be determined.

| Object | Source lines |
|---|---|
| Smooth four-dimensional background, admissible vacuum sequences, auxiliary metric/derivative norms | 90–112 |
| Punctured cotangent bundle, positive-ray unit section, Hamiltonian/vector field | 114–125 |
| Einstein second moments, ray-measure transport, one-homogeneous tests | 126–135 |
| Full-momentum measure, local second moments, compact-support transport tests | 150–167 |
| Indices, ordered symmetric-index sums, volume density, inner products, local coordinate norms | 331–350 |
| Tensor defects, covariance conventions, Ricci-symbol kernel, physical quotient | 392–428 |
| Fourier conventions, bilinear multipliers, trilinear forms | 539–562 |
| Triple low/high partitions, caps, thin-cone thickness, normalized variables | 895–1024 |
| Independent-variable correction extension, spherical harmonics, BS^1 seminorms | 1248–1377 |
| Euclidean gauge-complement projection and fixed infrared regularization | 1621–1642 |
| Einstein-Hilbert action, density Euler expression, Hessian, physical contraction | 1747–1788 |
| Complete cubic variation, frozen Fourier vertices, cyclic test factors | 1917–2009 |
| High-frequency physical/gauge splitting, gauge potentials, screen projections | 2013–2107 |
| Gauge correction, physical far-angle correction, complete frozen-energy splitting | 2265–2641 |
| Homogeneous energy on Cauchy sections, flow-invariant section, weighted pushforward | 2993–3039 |

## Meaning of this record and next entry points

`source-index.json` retains locked identity, full section hierarchy,17 formal-result labels/titles/ranges and argument locations,2 remarks,33 unnumbered candidates,15 definition/notation candidates,87 source labels, and6 bibliography keys. Bibliography entries are only indexed; no online verification, full-text acquisition, or citation-sufficiency judgment was performed.

Before formalization, this index can support separate correspondence records between complete statements and actual Lean types, checking assumptions/scopes/dependencies individually. That work has not yet occurred. All results/candidates remain unmodeled/unformalized. This pass did not alter the source, create/modify the Burnett project itself, install dependencies, access the network, or publish.

**Delivery type: structural inventory, not independent Lean-correspondence review.**
