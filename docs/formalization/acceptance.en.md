# Paper Results Acceptance

[简体中文](acceptance.md)

The pinned manuscript's 17 numbered results and three approved unnumbered results have been formalized under the project's paper-results 1.2 standard. A single acceptance record lists the source location, Lean declaration, transitive axioms and review report for each of the 20 results. The scope includes the definitions and proof dependencies these results require. The source index lists the three illustrative appendix examples at lines 3430–3445. [Acceptance record](acceptance.json) · [Project scope](scope.json) · [Source index](../statements/source-index.json)

## Semantic review

The coordinator and three independent reviewers compared the actual Lean types, key definitions and proofs with the manuscript. On 2026-11-28, the project user reported that human semantic review had passed for all 20 results and their interpretations in the review packet. The acceptance record identifies that packet, the type probe and its log, and the individual reports by hash. The earlier delegated confirmation of the trilinear counterexample is recorded in the history for that entry.

The cubic freezing lemma uses a local classical amplitude and weak pairing representation, with a fixed infrared-regularized frozen operator. The inhomogeneous cubic continuity and analytic correction results use fixed bounded-frequency regularizations. The main theorem uses one subsequence of the original sequence, one covariance and its physical measure for the Einstein moments, Hamiltonian transport and full-momentum lift on globally hyperbolic open regions. [Cubic freezing](../statements/original-cubic-freezing.en.md) · [Forward kinetic limit](../statements/original-forward-kinetic-limit.en.md)

The dependency review traced the appendix identities to their uses in weak Ricci curvature, strong H⁻¹ convergence and the quadratically weighted change of section. The acceptance record lists the scalar and Hermitian coefficient declarations for the commutator lemma. [Weak Ricci curvature](../statements/weak-ricci-identification.en.md) · [Local strong H⁻¹ convergence](../statements/geometric-Hminus-closure.en.md) · [Weighted change of section](../statements/weighted-auxiliary-section-change.en.md)

## Pinned version and reproduction

| Item | Version |
| --- | --- |
| Reviewed proof commit | [208064b36a5fa971ddad2f2f0e946c512d3c44c4](https://github.com/Oho1e/Burnett-conjecture/commit/208064b36a5fa971ddad2f2f0e946c512d3c44c4) |
| Reviewed Git tree | `5385d6090630f226d63550807d8a4990aa1301b1` |
| Manuscript SHA256 | `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| Lean | [4.24.0](../../lean-toolchain) |
| mathlib | [f897ebcf72cd16f89ab4577d0c826cd14afaafc7](../../lake-manifest.json) |

Install the pinned toolchain and dependencies as described in the README, then run the following from the repository root. GitHub Actions records separate receipts for the candidate merge commit and the actual main commit. [Reproduction instructions](../../README.md#reproduce-the-checks) · [Check workflow](../../.github/workflows/project-check.yml)

```sh
python scripts/check_slices.py --repo .
python scripts/test_slices.py
python scripts/check_project.py --repo . --timeout 7200 --build-timeout 14400
```

The main run for the reviewed proof commit checked 1,157 registered targets and their transitive axioms. The dependency audit checked 2,212 Lean sources. Trust policy A permits `propext`, `Classical.choice` and `Quot.sound`. The checker reports `machine-check-passed`. The project scope records acceptance and binds it to the machine receipt and the human semantic confirmation. [Main run and artifact](https://github.com/Oho1e/Burnett-conjecture/actions/runs/46115144766) · [Acceptance record](acceptance.json)
