# Independent reverse verification of the Ricci-symbol fragment

Review date:2026-11-15. Scope is only fixed-point real algebra in `Burnett/Algebra/RicciSymbol.lean`, especially the noncharacteristic branch at source452. This is neither whole-paper coverage nor a main-theorem success/author-confirmation record.

**Verdict: independent semantic correspondence passes for this real, noncharacteristic, diagonal-elimination fragment; independent source compilation/type/transitive-axiom probes also pass on fixed versions.** The full432–465 expansion, polarization, null branch, and physical-quotient nonnegativity lie outside the proved scope. The first probe used a read-only parent-workspace path with every package version checked. Once this project's official cache was ready, the same frozen source/probe passed again in its independent dependency environment. Finally, source normalization limited to line endings/trailing whitespace was independently compared and rerun successfully in the project environment. Each run retains separate evidence below; no whole-project or whole-paper pass is claimed.

## Independence and inputs

Actual Lean was read first and its meaning written before comparison with the locked source. Initial readback is `.project-verification/reverse-ricci/initial-readback.md`. Neither `.project-verification/forward/`, forward explanations, nor other agents' conclusions were read. Project rules/standard/general state set scope, not mathematical correctness.

| Input | Identity |
| --- | --- |
| Locked `paper/burnett.tex` | SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| Current `Burnett/Algebra/RicciSymbol.lean` | SHA256 `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`; only line endings/trailing whitespace normalized, as in the final appended record |
| Initially reviewed implementation | SHA256 `60683d4f8d9f4d80cf39511f0669407dd67e8613006901c87008ff51f2ba2d95`; original bytes in `.project-verification/reverse-ricci/RicciSymbol.snapshot.lean` |
| Current implementation snapshot | `.project-verification/reverse-ricci/RicciSymbol.current.snapshot.lean`, same hash as current implementation |
| Source comparison | 415–465, plus four-dimensional Lorentz background99–114 and index/summation conventions334–338 |
| Lean | `leanprover/lean4:v4.24.0` |
| Fixed Mathlib | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |

## Mathematical proposition read from actual definitions

All quantities are at one point. Indices are $I=\{0,1,2,3\}$. `Covector` is $I\to\mathbb R$ and `Tensor2` is $I\times I\to\mathbb R$, with no type-level symmetry. Let $G^{ab}$ be `gInv` components. The actual definitions are

$$
\xi^a=\sum_dG^{ad}\xi_d,\qquad
k_c{}^a=\sum_dG^{ad}k_{cd},\qquad
s=\sum_{a,b}G^{ab}\xi_a\xi_b,
$$

$$
t=\sum_{a,b}G^{ab}k_{ab},\qquad
q_b=\sum_a\xi^ak_{ab},\qquad
\mathcal R_\xi(k)_{ab}=\frac{s k_{ab}+\xi_a\xi_bt-\xi_aq_b-\xi_bq_a}{2}.
$$

Every sum covers the full index set; double sums include all ordered pairs, not only the symmetric upper triangle, with no extra division by two.

The first main claim is: for arbitrary real array $G$, real covector $\xi$, and real array $k$, if $s\ne0$ and $\mathcal R_\xi(k)_{ab}=0$ for every $a,b$, then the array identity

$$
k_{ab}=\xi_av_b+v_a\xi_b,\qquad
v_b=\frac{q_b-t\xi_b/2}{s}
$$

holds. This is all of `kernel_eq_pureGauge`; it does not say every gauge tensor conversely lies in the Ricci kernel. The proof rearranges $2\mathcal R=0$ and divides by nonzero $s$, without symmetric/nondegenerate G or assumed symmetric k. The conclusion itself makes kernel k symmetric.

One cannot add the converse for arbitrary nonsymmetric $G$. Let $G^{00}=G^{01}=1$, all other entries zero, $\xi=(1,0,0,0)$, $v=(0,1,0,0)$, and $k=\xi\otimes v+v\otimes\xi$. Then $s=t=1$ but $\mathcal R_\xi(k)_{00}=1/2$. The theorem name must be read as its actual one-way type. The source uses a true symmetric inverse metric and needs exactly that proved direction at452.

Subsequent definitions are

$$
c(k)^a{}_{bc}=\frac{\xi_bk_c{}^a+\xi_ck_b{}^a-\xi^ak_{bc}}2,
$$

$$
B_{bc}(k,k)=\sum_{a,e}\left(c(k)^a{}_{ce}c(k)^e{}_{ba}-c(k)^a{}_{ae}c(k)^e{}_{bc}\right).
$$

Lean separately proves the linear raising expansion, the gauge connection-symbol formula, and quadratic elimination:

$$
c(\xi\otimes v+v\otimes\xi)^a{}_{bc}=\xi_b\xi_cv^a,
\qquad B_{bc}(\xi\otimes v+v\otimes\xi,\xi\otimes v+v\otimes\xi)=0.
$$

The two summands are equal at every ordered $(a,e)$, so quadratic elimination loses no summation order, truncation, or sign. Final `quadraticSymbol_eq_zero_of_noncharacteristic_kernel` substitutes the gauge representation to obtain

$$
s\ne0,\quad \mathcal R_\xi(k)=0
\quad\Longrightarrow\quad
\forall b,c,\ B_{bc}(k,k)=0.
$$

Actual `#check @...` confirms no extra geometric, regularity, existence, or unproved-conclusion parameters beyond the listed $G,\xi,k,s\ne0,\mathcal R=0,b,c$. Real-field/finite-sum library structure is fixed by the types, not extra caller assumptions. Complete type/axiom output is in the logs below.

## Itemwise comparison with the locked source

| Item | Judgment and reason |
| --- | --- |
| Four-dimensional real components | Source99–101,334 uses Lorentz-metric components in four dimensions; `Fin 4` supplies exactly four indices, representing only pointwise real components. |
| Raising indices | `raiseCovector` is $G^{ad}\xi_d$ and `raiseSecond` is $G^{ad}k_{cd}$, matching $\xi^a,k_c{}^a$; source symmetry of k removes any transpose difference. |
| $q,t,s$ and Ricci symbol | Exact match to416–417, including $1/2$, both minus signs, and free-index positions. |
| Ordered sums | Double sums in $t,s,B$ cover all ordered pairs, matching335,428 and retaining off-diagonal symmetric-tensor multiplicity. |
| Denominator | v uses the same `symbolNorm`, with actual $s\ne0$; real2 is nonzero. Lean's default division at zero is not used for a null-cone conclusion. |
| Gauge representation | The452 implication $\mathcal R=0\Rightarrow k=\xi\otimes v+v\otimes\xi$ and explicit v agree. No converse is required there or provided by Lean. |
| Connection symbol/B order | Matches434–435, especially $c^a{}_{ce}c^e{}_{ba}-c^a{}_{ae}c^e{}_{bc}$ order/minus sign. |
| Real diagonal elimination | The c formula and $B(k,k)=0$ hold for any real gauge amplitude, hence eliminate the noncharacteristic kernel. |
| Mixed/complex amplitudes | No bilinear/Hermitian polarization is defined. The final real-diagonal result cannot be registered as including all original mixed terms. |

### Applying general arrays to an actual inverse Lorentz metric

“More general” alone is insufficient. At each original point x in a coordinate basis, insert actual inverse components $G^{ab}=g^{ab}(x)$ and actual real covector/symmetric-tensor components $\xi_a,k_{ab}$. Every definition becomes original $\xi^a,k_c{}^a,s,t,q,c,B$, with no Euclidean-identity replacement or metric-diagonalizing basis. Original $s\ne0$ and $\mathcal R=0$ give exactly the two premises. Thus this applies to general inverse Lorentz metrics pointwise, not just constant Minkowski data.

The source constructs no geometric metric object and proves neither inversion of a covariant metric nor coordinate naturality. That is a component-model boundary. This algebra applies to supplied actual inverse components pointwise without another inversion theorem, but manifold-level/coordinate-free Lean claims require actual bridges; this explanation is not a formalized geometric theorem.

The source also writes both full products as $\xi_b\xi_c(\xi^av_a)^2$. Code directly proves termwise cancellation of their difference, without separately proving that square formula. Actual definitions sum each to $\xi_b\xi_c(\xi_av^a)^2$; for the symmetric inverse metric, $\xi_av^a=\xi^av_a$, so no sign conflict arises. The larger nonsymmetric-array domain is not the source's Lorentz-geometric domain.

### Mathematical self-checks

Under $k\mapsto\lambda k$, $t,q,\mathcal R,v,c$ have degree1 and B degree2. Under $\xi\mapsto\mu\xi$, $s,\mathcal R,B$ have degree2, $q,c$ degree1, and noncharacteristic v degree−1, so gauge representation has the correct degree. The denominator respects the s=0 boundary.

Premises allow nonzero data: take $G=\operatorname{diag}(-1,1,1,1)$, $\xi=(1,0,0,0)$, $k_{01}=k_{10}=1$, all other k zero. Directly $s=-1,t=0,q=(0,-1,0,0),\mathcal R=0,v=(0,1,0,0)$, yielding nonzero pure-gauge k. This manual check rules out vacuity, not replaces general Lean proof. Conversely G=0 or ξ=0 gives s=0 and cannot use the theorem. No nonsymmetric-k kernel direction is missed: antisymmetrizing $\mathcal R=0$ gives $s(k_{ab}-k_{ba})=0$, so nonzero s forces symmetric k.

## Source conclusions not covered

The following are not formalized by this file and remain future targets:

1. Source437–449: $K_2,(k^2)$, nine-term expansion, $c(k)^a{}_{ae}=\xi_et/2$, and full `eq:B-algebra`.
2. Source450,452: bilinear mixed elimination, Hermitian polarization, complex amplitudes. Appropriate polarization yields them mathematically, but no Lean objects/proofs yet exist.
3. Source454–458: equivalence of the s=0 kernel with $q=t\xi/2$ and `eq:B-null`. Nonzero ξ remains needed on the cone; s≠0 here excludes that branch and cannot replace its argument.
4. Source459–463: physical/gauge mixed cross elimination $F(k,\ell)=0$.
5. Source465: null frames, independently removable gauge components, trace-free-screen representatives, physical-quotient nonnegativity/representative independence.
6. Source414,421–428: analytic derivation of kernel constraints from defects, positive Hermitian measures, r-isometries/covariance; also measure support, limiting Ricci, or main-theorem conclusions.

Thus all of `unnum:quadratic-symbol-algebra` (432–465) remains partial. The passing scope is precisely real gauge representation and diagonal quadratic elimination on the noncharacteristic Ricci kernel.

## Machine review record

### First probe: read-only parent-workspace path

Actual SDK: `D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe`, reporting Lean4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. `.project-verification/reverse-ricci/Probe.lean` directly includes actual source followed by `#check @...` for every definition/theorem and five `#print axioms`, avoiding stale project `.olean` files.

To avoid blocking on this project's official targeted-cache download, authorized read-only library objects under `D:\Chatpgt\Lean形式化\.lake\packages\<package>\.lake\build\lib\lean` were used. All nine manifest packages were checked beforehand: actual parent HEADs matched locked revisions and tracked sources were unchanged. `Cli` had no usable build directory, so was omitted; this fragment's closure does not need it. No shared cache was copied/written/replaced, no Lake update ran, and no project configuration changed.

Actual command, run in the project with `LEAN_PATH` set as recorded:

```powershell
& 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe' `
  -o '.project-verification/reverse-ricci/Probe.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**Actual exit code0.** Source/implementation/probe post-run hashes still match bound inputs. Probe SHA256 `7706ee9e830aa6eb59cfd0876f421ba137c213e631582d36ed5a4ca9f69afc94`. No warnings/errors; all five transitive-axiom sets are exactly

```text
propext, Classical.choice, Quot.sound
```

No `sorryAx` or added mathematical axiom appears. This reports actual dependencies, not user approval of the final trust policy.

| Local evidence | Contents |
| --- | --- |
| `.project-verification/reverse-ricci/initial-readback.md` | Mathematical readback formed before source comparison |
| `.project-verification/reverse-ricci/inputs.json` | Pre-run source/implementation/config hashes and actual SDK/Mathlib versions |
| `.project-verification/reverse-ricci/readonly-fallback-package-heads.json` | Nine locks, actual HEADs, tracked-source state, build-directory availability |
| `.project-verification/reverse-ricci/readonly-fallback-lean-path.txt` | Actual read-only runtime imports |
| `.project-verification/reverse-ricci/probe-readonly-fallback.log` | Complete actual types and five axiom sets |
| `.project-verification/reverse-ricci/probe-readonly-fallback-result.json` | Actual command/times/exit/source/probe/log hashes |

These record independent compilation, not this project's own Lake build, target registration, or full machine entry-point checks.

### Additional rerun: this project's independent dependencies

On2026-11-15 (UTC `2026-11-14T18:25:36.6824689Z`–`2026-11-14T18:25:52.1587554Z`), after official project caches were ready, all nine actual package HEADs again matched the manifest and tracked sources were unchanged. Inherited `LEAN_PATH` was cleared for that subprocess; SDK bin was prepended only to that PowerShell subprocess's PATH, and project `lake env` supplied imports.

Actual command:

```powershell
$projectSdkBin = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin'
$env:PATH = $projectSdkBin + ';' + $env:PATH
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
& "$projectSdkBin\lake.exe" env "$projectSdkBin\lean.exe" `
  -o '.project-verification/reverse-ricci/Probe.project.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**Actual exit0 again, no warnings/errors.** Third-party imports were under `D:\Chatpgt\Lean形式化\Burnett-conjecture\.lake\packages\`, with this project's build directory/SDK standard library, not parent-workspace package builds. No further cache download/copy/config change occurred.

As before, every definition/theorem type matches readback; all five axiom sets are exactly `propext, Classical.choice, Quot.sound`, without `sorryAx` or added mathematical axioms. Both complete stdout logs have SHA256 `03a869cc1f9aede07957022522bfe89037d8e10ea65bbec4fba2fb19e9a453bf`.

Article, frozen implementation, original probe, toolchain, lakefile, manifest, and scope hashes were unchanged before/after. Source/implementation/probe remain `e5e9fc…`, `60683d…`, `7706ee…`; scope SHA256 `81651a0da2c7090e336c289faed1aa3685a54dda937c5d64aa61455b07e58668`. Full values/package revisions are saved. Added scope support targets do not enlarge mathematical review scope.

| Added evidence | Contents |
| --- | --- |
| `.project-verification/reverse-ricci/project-probe-inputs.json` | All input hashes, actual nine-package HEADs/tracked states |
| `.project-verification/reverse-ricci/project-lean-path.txt` | Actual independent imports supplied by project lake env |
| `.project-verification/reverse-ricci/probe-project.log` | Repeated complete actual types/five axiom sets in project environment |
| `.project-verification/reverse-ricci/probe-project-result.json` | New command/times/actual0/pre-post bindings/log hash; `fallback_used: false` |

This removes the first run's parent-build-path limitation while retaining it historically. The actual run is a frozen-source probe in project dependencies; full builds/target entry points have separate execution records.

### Final source binding: line endings/trailing whitespace only

After formatting, implementation SHA changed from `60683d4f8d9f4d80cf39511f0669407dd67e8613006901c87008ff51f2ba2d95` to `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`. Without reading forward evidence, the reviewer directly compared current source to its own original `RicciSymbol.snapshot.lean`; the actual assertion

```text
current_source == old_source.Replace(CRLF, LF).TrimEnd() + LF
```

passed. Changes are exactly CRLF→LF and trailing file whitespace; definitions/types/proofs/meaning are unchanged, so semantic review carries over without a full mathematical rereview. Original probe bytes are separately retained as `Probe.pre-format.lean`, SHA256 `7706ee9e830aa6eb59cfd0876f421ba137c213e631582d36ed5a4ca9f69afc94`, keeping original paths/hashes in earlier evidence. Current `Probe.lean` combines current source with the unchanged query suffix, SHA256 `02c44241376378abc6deae91dec36ce4c1378045a744c2a030413611176a4b88`.

On2026-11-15 (UTC `2026-11-14T18:29:47.7977256Z`–`2026-11-14T18:30:04.7173462Z`), still using only independent project dependencies, the actual rerun was:

```powershell
& 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe' env `
  'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe' `
  -o '.project-verification/reverse-ricci/Probe.current.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**Actual exit0, no warnings/errors.** Stdout for actual `#check @...` types and five `#print axioms` is byte-identical to pre-format output, SHA256 `03a869cc1f9aede07957022522bfe89037d8e10ea65bbec4fba2fb19e9a453bf`. The same three axioms remain, no `sorryAx`; pre/post input hashes all match, article/config unchanged.

| Additional current-source evidence | Contents |
| --- | --- |
| `.project-verification/reverse-ricci/current-source-inputs.json` | Independent formatting assertion, old/current source/probe hashes, other bindings |
| `.project-verification/reverse-ricci/RicciSymbol.current.snapshot.lean` | Current actual source bytes |
| `.project-verification/reverse-ricci/Probe.pre-format.lean` | Original probe retained completely for the first two runs |
| `.project-verification/reverse-ricci/current-source-lean-path.txt` | Actual project import path of this run |
| `.project-verification/reverse-ricci/probe-current-source.log` | Current actual types/transitive axioms |
| `.project-verification/reverse-ricci/probe-current-source-result.json` | Actual command/times/exit/pre-post/output bindings |

## Confirmation and status

Independent mathematics found no substantive mismatch for this real noncharacteristic fragment; source/type/axiom probes actually passed in both environments. User/author confirmation of the ordinary explanation still had not arrived at this appendix. This record fabricates none and declares neither whole-paper coverage, approved final trust, nor main-theorem success.

## 2026-11-15: second cross-discussion requested by the user

The user's actual reply was “Ask subagents to discuss and check.” This authorizes further independent review, not author confirmation. Inputs remain the listed source `e5e9fc…`/implementation `f9cfae…`. No article, Lean definition/theorem/proof, dependency lock, or target manifest changed.

### Independent evidence and cross-challenges

- In a new context, `ricci_type_readback_v2` first read actual Lean, froze ordinary-mathematical readback of all definitions/five theorems, then read source400–475 and conventions without borrowing prior verdicts.
- In a separate new context, `ricci_paper_adversary_v2` extracted claims first from390–480/conventions, then read Lean; it independently checked raising, product order, implication/equivalence, and real/complex boundaries.
- After independent judgments, they exchanged disputes/counterexamples and checked root's exact source-definition examples. Verdicts below use actual identities/counterexamples, not agent agreement or historical CI as proof.

### Re-expanded core proof

For each $a,b$, $\mathcal R_\xi(k)_{ab}=0$ gives

$$
s k_{ab}=\xi_aq_b+\xi_bq_a-t\xi_a\xi_b
=s(\xi_av_b+v_a\xi_b),\qquad
v_b=(q_b-t\xi_b/2)/s.
$$

The explicit $s\ne0$ makes cancellation legitimate. Raising the second index gives $k_c{}^a=\xi_cv^a+v_c\xi^a$; substitution into original c cancels cross terms, yielding $c(k)^a{}_{bc}=\xi_b\xi_cv^a$. Thus B's two terms at each ordered $(a,e)$ are

$$
(\xi_c\xi_ev^a)(\xi_b\xi_av^e),\qquad
(\xi_a\xi_ev^a)(\xi_b\xi_cv^e),
$$

They are equal termwise, so their summed difference vanishes. No prior symmetric G/k is needed; choosing actual inverse Lorentz G applies it pointwise.

### Disputes, counterexamples, and verdicts

| Challenge | Actual check and resolution |
| --- | --- |
| Do general real arrays change the claim? | Contractions/free indices/$1/2$/minus signs/full ordered sums match the source. $G^{ab}=g^{ab}(x)$ recovers its components, with no identity-matrix substitution or claimed manifold inversion/naturality bridge. |
| Does the name imply kernel equals all pure gauge in both directions? | Actual type only gives kernel $\Rightarrow$ explicit gauge. For nonsymmetric G the converse may fail: identity plus $G^{01}=1$, $\xi=e_0,v=e_1$ has s=1 but $\mathcal R_\xi(\xi\otimes v+v\otimes\xi)_{00}=1/2$. The name adds no set equivalence. |
| Does the square form of both source products match? | Direct sums naturally give $\xi_b\xi_c(\xi_av^a)^2$, versus source $\xi_b\xi_c(\xi^av_a)^2$. Actual inverse symmetry equates them. For nonsymmetric G/arbitrary gauge tensors they cannot simply be interchanged, but this neither refutes termwise cancellation nor requires added symmetry in the kernel claim. The five theorems do not separately assert either square value. |
| Are all mixed terms of452 covered? | No: current definitions/final theorem give only real diagonal $B(k,k)$, with no bilinear/Hermitian polarization or measure conclusion. Source450 and final sentence452 remain obligations. This target is the real noncharacteristic diagonal subclaim of452. |
| Is $s\ne0$ dispensable? | No. Take $G=\operatorname{diag}(-1,1,1,1)$, $\xi=(1,1,0,0)$, $k=\operatorname{diag}(0,0,1,-1)$. Then s=t=q=0 and Ricci symbol0, but $B_{00}(k,k)=1/2$. Indeed $c(k)^e{}_{00}=0$, $c(k)^a{}_{0e}=k_e{}^a/2$, making the first sum $(1+1)/4$. Both agents independently checked this. |

Root used Python standard-library `Fraction` to reconstruct three exact component checks from source definitions: nonzero Lorentz noncharacteristic gauge data, the nonsymmetric converse counterexample, and the null example. `.project-verification/ricci-cross-review/exact_checks.py` actually exited0, with `exact-checks.json` there. These finite examples check boundaries, not general identities or new Lean targets. No unchanged Lean build was repeated; earlier fixed-source evidence retains its original bindings.

**Verdict: the five current declarations accurately cover the stated real noncharacteristic diagonal subclaim, with no defect requiring changed implementation or added assumptions.** Full expansion, mixed/Hermitian polarization, null and geometric/measure bridges remain unfinished. Author confirmation awaits an actual answer; this cross-discussion replaces neither human confirmation nor whole-paper coverage.
