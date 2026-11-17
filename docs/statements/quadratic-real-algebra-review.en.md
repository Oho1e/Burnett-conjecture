# Independent readback of parallel real-algebra fragments

Date:2026-11-15. Source SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. This covers only four new real-algebra results at source432–463, not all F06, article results, or human confirmation.

## Frozen inputs

| Source | SHA256 |
| --- | --- |
| `RicciSymbol.lean` | `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8` |
| `QuadraticDefs.lean` | `f6261b4f7d3a926ce44aa07fec7b6b367fa6e376f61ccce52c99b6a65e4e4e09` |
| `QuadraticExpansion.lean` | `fbb166ba88ed619083c283ef4c43650d9e406d199b2d65c538e244cceeca622c` |
| `NullKernel.lean`, final v2 | `972856c53a3f4c61c1f3dccb63c91ffa119b76b2a6e2dd8861af03975cd86b7d` |
| `NullQuadratic.lean` | `3dad381221de18430c5f7127fb496065b5bbcf2f06e43c5c5d2d0be91bbc78e7` |

`parallel_null_reverse` first read frozen-v1 actual types and definitions, then compared the source. After implementation continued, it independently checked v2 additions and unchanged v1 body. `parallel_b_reverse` froze its B readback before reading the implementer explanation, then checked the source and root's NullQuadratic assembly. Implementer compilation did not replace independent readback.

## Actual mathematical meaning and boundaries

G/k are real four-dimensional arrays. Symmetry is an explicit component assumption, not a hidden metric field. Every sum covers all ordered indices. The shared contraction is `k_ab l^{ab}`; F subtracts half the trace product from this real bilinear contraction, not a positive Euclidean inner product or complex Hermitian form.

- The full4B expansion needs only symmetric G/k, not a Ricci kernel, s=0, signature, or nondegeneracy. Actual inverse-metric components instantiate it directly; both symbol products, signs, and coefficients match source447–448.
- For nonzero ξ and s=0 the Ricci kernel is equivalent to q=tξ/2. Unit cosphere ensures nonzero ξ; the proof selects an existing nonzero component rather than fixing a coordinate. Symmetric G/k are not required.
- Real physical/gauge cross elimination requires symmetric G/k and those null-kernel conditions, with arbitrary real v. Symmetry enters the corresponding contraction/trace formulas and cannot simply be deleted. The proof gives F(k,ξ⊗v+v⊗ξ)=0, not merely zero gauge self-pairing.
- The combined formula substitutes the actually proved kernel constraint into the proved B expansion, giving B=ξ_bξ_cF(k,k)/4. Neither branch assumes the null B formula.

The null reviewer independently reconstructed six exact boundary examples: the kernel equivalence generally fails without s=0, and cross elimination can give nonzero F without symmetry. This particular equivalence also holds at ξ=0, but retaining nonzero ξ follows the article's objects instead of adding irrelevant generalization work.

## Checks and verdict

Independent source compilation, actual types, and transitive-axiom probes for all5 public declarations of null v1/v2 exited0, depending only on `propext`, `Classical.choice`, and `Quot.sound`. Readback, frozen-copy differences, types, axioms, and counterexamples are in `.project-verification/parallel-pilot/reverse-null/`; the formal report is `REVERSE_REVIEW.md`.

Independent B/combined-formula readback and isolated probes passed. All five production sources, two actual type/expansion probes, and SDK calls exited0 with unchanged pre/post hashes, using only those three axioms. The first independent probe exited1 because pp.width was invalid; a full rerun with format.width passed and the failed log remains. Verdict: `.project-verification/parallel-pilot/reverse-b/review-result.txt`; machine binding: `machine-evidence.json` there; type/definition outputs: `ReverseAudit.log` and `ReverseNullAudit.log`.

Root's combined full-library build and actual type/transitive-axiom probes for the four new targets also passed. There is no `sorry`, added mathematical axiom, or native_decide. All9 registered support targets passed unified existence/source/axiom audits with actual exit0; the [persistent machine record](../formalization/parallel-machine-evidence.json) retains inputs. Remote CI is observed against actual commits separately. Author confirmation remains pending and is not replaced by this record.

General polarization/complex Hermitian extension, null physical-quotient positivity/general Lorentz null-frame bridges, covariance/measure applications, and F04/F05/F07 closure remain unfinished. The branches and combined formula do not complete F06.
