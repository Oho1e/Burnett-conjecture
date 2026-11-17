# First foundations batch: independent readback and integration record

Date:2026-11-16. Article SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`; code baseline is merged PR5 `242eebe9d87ef62c15efab8df7741051f0aed260`.

Actual implementation, independent readback, combined machine checks, and publication are recorded separately. All14 mathematical sources are frozen and rolling independent readbacks passed. No whole-paper tag is issued and no older main/PR green is used as current evidence.

## Independent readback

N1/N2/N3 implemented Fourier/off-cone tools, pointwise geometry, and a common subsequence respectively. N3 independently read N2's actual source/definitions against the article/old F06; N2 similarly read N1's frozen files. Root did not construct CountableTests and independently read actual types and recompiled its source/axiom query.

| Module | Frozen source SHA256 | Independent checks in this batch |
| --- | --- | --- |
| CountableTests | `0897e00360d3db4821640bb31ce813dd7013f506d2e318bcc6933f1d5844b892` | root actual compilation and complete type/axiom checks exit0; same subsequence and retained limit bounds; not a full microlocal measure |
| FiberMetric | `b574e597c29b8bac5f6f17c09bc1817a87b5ea8bab9f02a4a372c4bb18a8d522` | N3 fresh independent compilation exit0; general-g G⁻ᵀ distinguished from symmetric-g G⁻¹ |
| BasisFrame | `af704f4b469ddbb9a44235707572d9a34881c63d2dad6b2c38fa6a0331018364` | N3 fresh compilation/all-public-declaration queries exit0; actual basis changes and supplied orthonormal basis to old certificate; beyond-pointwise scope open |
| OffNullGeometry | `79b26ceb0b2158b4792d4361458cfd3e6f6bc83e542aa085878c0194d01657c7` | N2 independent compilation/check exit0; actual same-f/w frequencies, fixed δ, whole-space separation correct |
| SchwartzTail | `3359c56b998114a9a22d3e651b3df97f1e2d1bd923de79fe9c8cc17447a59a99` | N2 compilation/check exit0; actual Fourier-square integrability and full-space vanishing tails; no arbitrary polynomial rate claimed |
| SchwartzParseval | `2d729ee3943f10f2fc4f5b5757d7aaeafc82c29599da02f9331c9cad3d37fd1e` | New independent Fourier reviewer recompiled/all-declaration axioms exit0; conjugation, integral interchange and inversion direction correct |
| OffNullCutoff | `facf6f8063d63aa3871b1f1e83320302eeb1eab67d807b42081c164842e778db` | N2 literal unfolding/compilation/axioms exit0; actual product error strongly vanishes in L², without nonlocal commutation |
| Modulation | `51adc4dd13038d069a87458eade548ff763de38c6ec7a0b5656991927f985b75` | New Fourier reviewer compilation/check exit0; positive-exponent modulation gives ξ−k, angular frequency divided by2π |
| OffNullTail | `bc72b6690360cd19426c7c35be4978003fd7c1475e0ba4ffe06f89f157f1ad00` | New Fourier reviewer compilation/check exit0; fixed δ, real scaling, both frequency signs, full Eδ integral correct |
| Cosine | `e499fcf401423368f5a9914f224d9b6ff5672016ea87d1d241bf0670aceedfb6` | N3 full-source compilation/public queries exit0; actual cosine to two modulations with explicit L¹ assumptions |
| FiniteEnergy | `f82f67d3f121b3133e5b87f12f63b0c7292b3c6a687cb8f2a78cc7cad9c7fcfc` | N3 compilation/check exit0; square integrability precedes finite-energy comparison, no default zero |
| OffNullGradient | `69065cf1a1c22376505b6409c80562ac6bf42c059eb0c7b04c1c4553bcc29822` | N3 compilation/check exit0; actual same-f/w finite modes, coefficients and frequency normalization correct |
| OffNullCompactGradient | `8aa20edd64e304a224fefd41e37ce57494280f9556a43df7f0bab6d4c87c73d5` | N3 compilation/check exit0; every original real C∞c cutoff, fixed δ, all-four-component full Eδ energy; no physical projection constructed |
| OffNullGradientBridge | `c9a0b506f1237503b7f19358a10c129593ac31abad838e9849ef98cabb02d34e` | N2 compilation/check exit0; actual L² a.e. difference and fixed-CLM conclusion; A remains explicit |

N3 checked30 public declarations across the two geometric files using only the three axioms, additionally proving symmetry of g from the supplied covariant Lorentz orthonormal identity, avoiding confusion with general nonsymmetric forms. N2 checked11 key actual types/transitive axioms across the first two files with the same three axioms. Logs/source bindings remain in workspace evidence; actual complete-entry/target/additional-definition checks follow below.

N3 also independently read four terminal mode/gradient modules, with23 public declarations and full-source compilation exit0. N2 additionally read two cutoff modules, with18 declarations/definitions and compilation exit0. These confirm the distinct scopes of frequency energy and actual L² position bridges, not an as-yet-unconstructed Fourier projection assembled from them.

The newly assigned independent Fourier reviewer had not constructed the sources. It recompiled a seven-module local dependency closure and checked12 theorems plus modulate in Parseval/Modulation/OffNullTail, all exit0 with only three axioms, confirming conjugation, normalization, integrability, and full-space scope. The initial probe's missing-dependency-olean failure remains recorded; only the corrected full local closure passed, without changing production cache. Frozen inputs have matching pre/post hashes.

## Inheritance and remaining work

Old F06 algebra, the12 old X02 mathematical modules, article, and locks remain unchanged. New entry points import only additions. Earlier semantic confirmations carry over only with unchanged actual types/definitions/explanation scope; local delegation does not expand to these results or the whole article.

New support lemmas may enter development main; this record does not claim personal user/author review of these Lean statements. Ambiguous source assumptions or changed conclusions still go individually to the user. No issue requiring changed source assumptions to implement these support results has been found in this batch.

F05 PDO boundedness, dense-test extension, positivity, and bundle-valued measure extraction/localization remain open. N2 still needs orthonormal-basis existence, smooth selection, and global geometric integration. Full X02 still needs actual L² Fourier extension/projection models and compatibility. Schwartz Parseval, modal frequency energy, or small cutoff error under an arbitrary fixed CLM cannot substitute for those.

## Machine and remote checks

The35 new support targets enter one candidate with actual code, entry points, inventory, and slice locations:137 targets/209 inventory entries/47 Lean sources. Complete entry build,137 actual target/transitive-axiom checks, and47-source dependency boundaries actually passed under snapshot-policy v2;17 slice regressions and46-slice/135-edge structure passed. The standard, nine-package lock, and clean dependency-source identities were checked.

Extra auditing checked actual types for122 public declarations in14 modules and transitive axioms for30 definitions/aliases including standardFiberFrame, exit0 with only three axioms. See the [extra-definition receipt](initial-foundations-extra-definitions.json). This is an actual local frozen-source check, not a claim GitHub ran the auxiliary probe.

After recording independent results, combined checks were actually rerun against final scope and machine receipts bound, exit0. Actual GitHub candidate CI is separately checked and recorded in external handoff. PR5's102-target receipt is not reused; this file does not embed its own containing commit SHA. A ready PR is not a merged PR; no main merge or tag is performed here.
