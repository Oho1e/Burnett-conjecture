# F06 real mixed polarization: independent reverse review of frozen sources

Date:2026-11-15. Role: independent reverse reviewer, uninvolved in forward construction.

Final verdict: **local independent semantic verification passes for the frozen version.** Actual source, central `#print` of important definitions, and `#check @` output for every public declaration were independently read. No coefficient/index/quantifier/assumption defect was found in this real mixed deliverable. Central type/axiom queries exited0 with all29 public declarations, each using exactly the standard three axioms. This reviewer did not personally run Lean, public Lake, or CI; independently inspected machine output and this reviewer's mathematical judgment are distinguished below.

## 1. Independence and actual operations

An independent `source-specification.md` was first written from source430–466 and kernel conventions414–428, before receiving frozen paths/SHAs. Working/frozen source hashes were then computed and matched before reading all327 actual lines and important imported definitions. Forward self-review/output conclusions/implementation summaries were not read. Ordinary mathematical meaning came from actual definitions/signatures, then comparison with the previously retained source specification.

No production source, scope, target registration, Git, article, toolchain, or dependency was modified; only mathematical specifications/review records in this `reverse/` directory were written. Lean was not run. Later, centrally generated actual query sources/type/axiom outputs from the coordinator were inspected directly, rather than relying on implementer summaries. Type-level judgment preceded reading the central ordinary-mathematical explanation for fidelity.

## 2. Input bindings

These SHA256 values were actually computed locally by this reviewer in stage2; source identity also matches stage1:

| Input | SHA256 |
| --- | --- |
| `paper/burnett.tex` | `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| `Burnett/Algebra/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `.project-verification/slice-workflow-test/forward/frozen-v1/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `Burnett/Algebra/RicciSymbol.lean` | `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8` |
| `Burnett/Algebra/QuadraticDefs.lean` | `f6261b4f7d3a926ce44aa07fec7b6b367fa6e376f61ccce52c99b6a65e4e4e09` |
| `Burnett/Algebra/QuadraticExpansion.lean` | `fbb166ba88ed619083c283ef4c43650d9e406d199b2d65c538e244cceeca622c` |
| `Burnett/Algebra/NullKernel.lean` | `972856c53a3f4c61c1f3dccb63c91ffa119b76b2a6e2dd8861af03975cd86b7d` |
| `Burnett/Algebra/NullQuadratic.lean` | `3dad381221de18430c5f7127fb496065b5bbcf2f06e43c5c5d2d0be91bbc78e7` |
| `lean-toolchain` | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| `lake-manifest.json` | `9de3b9d4ed07859ef9b086b79a49884daffcea2db2340514eb013242fca7aeaa` |
| `lakefile.toml` | `89aa753ae1715bf8d34bd31b94480fa2776fc22e85a802d2743f6ef92ded3e9e` |
| `.project-verification/slice-workflow-test/central/ActualTypes.lean` | `93198c1f3697c0ef06b6562d5bec71d05a7c028ec6e5f280aed62036bddb6eb4` |
| `.project-verification/slice-workflow-test/central/actual-types-and-axioms.log` | `7e0217ebe02a221f984824db990c3e2a9397aab32895aa22569f5df0c7095de2` |
| `.project-verification/slice-workflow-test/central/actual-types-receipt.json` | `4eb035a28887350522cd559c2472b0fdeb261ab764a85a06b6ab83bf734f4ce0` |
| `docs/statements/real-polarization.md` (explanation awaiting user/author confirmation) | `de1ca6bda24b85980fe45968869841696bac314187c83ddd8eeb63ad60d19edc` |

Stage1 specification: `.project-verification/slice-workflow-test/reverse/source-specification.md`, SHA256 `ab7be3fcc1ca84fb623dbea75cada47f31e010cbc72a594ebedfb9014f10a01a`. Scope is this local deliverable, not an independent inventory of the whole paper/all F06.

## 3. Objects independently read from actual definitions

`RicciSymbol.lean:14–18` fixes Index=`Fin 4`, four real Covector components, and four-by-four real Tensor2 component functions. Matrices are not structures carrying symmetry/nondegeneracy; needed symmetry must be explicit. `r • k`/`k+l` are componentwise real-function operations, without complex scalars/conjugation.

`raiseCovector`/`raiseSecond` actually contract with supplied gInv. `metricTrace`, `contracted`, `symbolNorm` are original t,q,s. `ricciSymbol` is416's `1/2(sk+ξξt−ξq−qξ)`; `connectionSymbol` is434's c(k). `quadraticSymbol` retains all ordered a/e values and the original product subtraction order (`RicciSymbol.lean:65–76`).

New `connectionCrossSymbol` (11–15) independently reads as

\[
C_{bc}(k,\ell)=\sum_{a,e}\left(c(k)^a{}_{ce}c(\ell)^e{}_{ba}-c(k)^a{}_{ae}c(\ell)^e{}_{bc}\right).
\]

Every index of the four connection-symbol occurrences matches source435: neither a different first contraction nor a reversed second-product sign. `mixedQuadraticSymbol` (19–22) reads as

\[
B^{\rm mix}_{bc}(k,\ell)=\frac{C_{bc}(k,\ell)+C_{bc}(\ell,k)}2.
\]

This symmetric mixed form is constructed from the original connection symbols, not a new B defined by the desired null-cone conclusion or an unrelated quadratic form.

In `QuadraticDefs.lean:13–22`, `tensorPairing=Σabcd g^{ac}g^{bd}k_ab ℓ_cd` and `physicalPairing= tensorPairing−tr_g(k)tr_g(ℓ)/2`, so actual F is exactly the real bilinear extension at457. All ordered indices remain; no a≤b-only sum or missing symmetric off-diagonal multiplicity.

## 4. Ordinary meaning and comparison by declaration group

| Actual declaration/lines | Reverse-read mathematical claim | Comparison to independent source specification |
| --- | --- | --- |
| `mixedQuadraticSymbol_comm`,118–122 | At fixed g/ξ/b/c, interchange any two amplitudes | Matches. Exchanges amplitudes, not b/c; no kernel/symmetry condition |
| `mixedQuadraticSymbol_add_left/right`,124–138 | Additivity in either amplitude slot | Matches for all real matrices/amplitudes |
| `mixedQuadraticSymbol_smul_left/right`,140–154 | B(rk,ℓ)=rB(k,ℓ), B(k,rℓ)=rB(k,ℓ) | Matches; explicitly real r, no kernel condition |
| `mixedQuadraticSymbol_diag`,157–161 | Bmix(k,k)=original quadraticSymbol(k) | Full diagonal bridge to original Q, not only a kernel special case |
| `mixedQuadraticSymbol_polarization`,165–174 | Bmix(k,ℓ)=[Q(k+ℓ)−Q(k)−Q(ℓ)]/2 | Correct factor for twice the cross term; a proved bridge, not a second arbitrary definition |
| `ricciSymbol_add/smul`,178–189 | Original Ricci symbol is real-linear in amplitudes | Matches; k+ℓ kernel membership is not hidden as a separate consumer premise |
| `mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel`,193–206 | Same g/ξ, s≠0, arbitrary independent k/ℓ each in the full Ricci kernel imply every b/c Bmix=0 | Covers all real mixed terms at452, not only k=ℓ or a preselected gauge amplitude |
| `tensorPairing_comm`, `physicalPairing_comm`,221–253 | Symmetric gInv gives symmetry of original contraction/F under arbitrary amplitudes | Matches; amplitudes need not be symmetric/in the kernel |
| `physicalPairing_add_left/right`, `physicalPairing_smul_left/right`,255–299 | F is linear in either real-amplitude slot | Correct; neither kernel nor symmetric-gInv conditions needed |
| `mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel`,303–325 | Symmetric gInv/k/ℓ, nonzero ξ, s=0, and both amplitudes in the same Ricci kernel give Bmix_bc(k,ℓ)=ξ_bξ_c F(k,ℓ)/4 | Matches real polarization at454–457; both1/4 and F's1/2 correct |

Auxiliary trace/q/connection/ordered-cross slot-linearity declarations concern these actual original definitions without replacing objects. There are no parameterized section variables, additional typeclass parameters, or assumption bundles. All central `#check @` complete types were checked for hidden strengthening; no conclusion is hidden in a new structure/class field.

Central log1–47 prints Index/Tensor2/Covector and original c/Ricci/tensorPairing/F/new C/M, matching Section3. Lines103–137 give M symmetry/bilinearity/bridge types;147–155 gives noncharacteristic elimination for any two kernel amplitudes;156–179 gives original contraction/F symmetry/real bilinearity;180–194 gives the null mixed formula with every actual premise. Neither core type adds assumptions beyond source/readback or loses independent k/ℓ and all-b/c quantifiers.

## 5. Assumptions, quantifiers, and dependency seams

The noncharacteristic theorem uses the same gInv/ξ. k/ℓ are independent, each with `∀ a b, ricciSymbol ...=0`; b/c are independently universal too. Different-frequency kernels are not mixed. An extra nonzero-ξ parameter is unnecessary since s≠0 excludes ξ=0. No Lorentz signature, nondegeneracy, symmetric inverse, or symmetric amplitude is needed. This legitimately stronger algebraic claim includes original real Lorentz data: the kernel constraints suffice, rather than omitting a necessary source premise.

The null theorem explicitly assumes symmetric gInv/k/ℓ, `ξ≠0`, `s=0`, and both full component kernel conditions. Both amplitudes must lie in the kernel; one cannot claim the formula with one arbitrary amplitude. There is no amplitude positivity/gauge-representative/F-nonnegative premise, nor an assumed Bmix=0 or target null identity.

Original nonzero ξ comes from the unit cosphere. The local theorem retains nonzero ξ without adding a unit-cosphere restriction. The trivial ξ=0 case could also be covered separately, but keeping the original condition is accurate. Absence of Lorentz-signature/nondegeneracy assumptions is a legitimate local-algebra extension; geometry still needs later bridges.

The null mixed formula uses the actual `NullQuadratic` diagonal formula with symmetric inverse/amplitude, nonzero ξ, s=0, and original kernel constraints. These are supplied for k,ℓ,k+ℓ. `physicalPairing_comm` explicitly uses symmetric gInv rather than misidentifying a nonsymmetric pairing as symmetric. No extra unproved mathematical interface remains here.

## 6. Independent coefficient/nonzero-amplitude check

Beyond source/implementation comparison, a nonzero example was manually checked from original c products: `gInv=diag(−1,1,1,1)`, `ξ=(1,1,0,0)`, with k/ℓ nonzero only in the2/3 screen block, respectively

\[
k_{\rm scr}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\ell_{\rm scr}=\begin{pmatrix}1&2\\2&-1\end{pmatrix}.
\]

Both independent amplitudes are nonzero, with t=q=s=0, hence in the same Ricci kernel. Full ordered contraction gives `F(k,ℓ)=1·2+1·2=4`, `F(k,k)=2`, `F(ℓ,ℓ)=10`. At b=c=0 the trace product vanishes; the first c product is one-quarter of the screen-matrix product trace, giving `C00(k,ℓ)=C00(ℓ,k)=1`. Thus Bmix00=1=`ξ0²·4/4`; the undivided cross sum is2=`ξ0²·4/2`.

The same diagonal formula gives `Q00(k)=1/2`, `Q00(ℓ)=5/2`, `Q00(k+ℓ)=5`, so `[5−1/2−5/2]/2=1`. This exposes missing off-diagonal multiplicity or cross-normalization errors. This finite manual check supplements, not replaces, the general Lean theorem/machine build.

Homogeneity also matches: for fixed g/ξ, Bmix is degree1 in either k/ℓ; for fixed amplitudes it is degree2 in ξ, matching the null right side.

## 7. Verdict boundaries and actual machine evidence

Final independent semantic verdict: the consumer deliverable covers original B's real symmetric mixed cross form, diagonal/polarization bridges, arbitrary two-amplitude mixed noncharacteristic elimination, null mixed B formula, and real bilinearity needed for Bmix/F. Actual types/important definitions were cross-checked against source, locked article, and stage1 independent specification, with no defect requiring changed statements or added assumptions.

Machine facts come from the coordinator's independently executed `lake env lean .project-verification/slice-workflow-test/central/ActualTypes.lean`; its receipt binds frozen-source SHA and log196 records `EXIT_CODE=0`. This reviewer extracted all29 public declarations and compared their set to29 query `#check @` and29 log `#print axioms` results: all sets match. Private helper `rp_sum_comm` is not counted as a public result. All29 axiom sets are exactly `{propext, Classical.choice, Quot.sound}`, without sorryAx, added axioms, or native_decide. Complete central build/project checker/CI are separately recorded by the coordinator; reading logs is not reported as personally running builds.

This verdict covers only frozen real local algebra. Without complex scalars/conjugation/sesquilinear declarations it does not close450's complex Hermitian obligation; without null frames/quotient/nonnegative/representative-independence results it does not close465's physical positivity. Geometry, measures, and later analysis remain open. F06 stays partial,17 numbered results incomplete, author confirmation pending, and final trust policy undecided at this stage.

## 8. Checking the ordinary mathematical explanation

After the actual-type judgment, all57 lines of `docs/statements/real-polarization.md` (input-table SHA) were read separately. C/M/Q normalization, symmetric-amplitude meaning, slotwise real linearity, both kernel conclusions,1/4 coefficient, ordered real F contraction, assumptions, and excluded scope accurately express the declarations, with no overstatement or missing necessary premise.

The explanation's9 main support and3 independent scalar-interface targets exactly match all12 then-registered `polarization:` targets;2 definitions/27 theorems match29 public declarations. At review time F06 was `partially_formalized` and17 numbered results `not_formalized`. This checks explanation/registration consistency, not independent scope auditing of all formal article results.

This is an identifiable explanation version, independently checked for accuracy and intended for user/author confirmation. Agent review does not produce that confirmation; it remains pending. Later mathematical/scope changes require impact review; wording/layout changes follow the workflow without automatically reopening all F06.
