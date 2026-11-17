# Audit of pinned Mathlib interfaces

[Chinese original](library-audit.md)

Audit date: 2026-11-15. The subject is the Mathlib checkout already present in the local parent workspace, **not an audit of the latest version**. This document reports only library identity, interfaces, and probe results. Existing project records manage dependency integration and paper-target status.

## Version and evidence boundaries

- SDK: `D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe`; actual output Lean **4.24.0**, compiler commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- Mathlib source: `D:\Chatpgt\Lean形式化\.lake\packages\mathlib`; actual Git HEAD **`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**, matching the parent workspace's `lakefile.toml` and `lake-manifest.json`; its source `lean-toolchain` is also 4.24.0.
- Git metadata, independent repository top levels, and worktree states were actually checked. Mathlib and the other 8 packages all have `.git`; each HEAD equals the parent manifest, and `git status --porcelain=v1 --untracked-files=normal` has no output in each. This follows from actual checkout inspection, not merely the manifest.
- The status check does not cover ignored build caches. Existing cache is incomplete; successful loading of some `.olean` files does not show that all caches were rebuilt from the current clean sources. This audit does not endorse complete cache provenance.
- SDK Lean was called directly, with `LEAN_PATH` pointing only to existing cache directories of 8 of the parent's 9 packages (`Cli` lacks that directory). No shared-library `lake build/update`, download, installation, or remote command ran. All probes/logs are under this project's `.project-verification/library-audit/`.

Local evidence: `source-identity.json` records package HEADs, locked values, origins, top levels, and worktree states. `module-evidence.json` records inspected module-source SHA256 values and `.olean` availability. `source-excerpts.log` retains line-numbered excerpts of the signatures below. After changing dependency integration, rerun affected checks in the new pinned environment.

## Near term: Ricci symbols and real finite-dimensional algebra

Paper location: `paper/burnett.tex:415–452`. Retain **Lean 4.24.0 + the Mathlib commit above** as the fixed baseline for the first algebraic interfaces: matching sources are present locally and the minimal probes below actually ran successfully. This does not establish library closure for the analysis.

Actually successful import group:

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
```

`AlgebraProbe.lean` / `AlgebraProbe.log` / `AlgebraProbe.result.json`: **exit 0**. Actual `#check` commands and nonempty example proofs covered:

| Interface | Verified signature/behavior | Near-term modeling use |
| --- | --- | --- |
| ℝ, Fin 4 | Real-number instances and finite indices available | `Fin 4 → ℝ`, `Matrix (Fin 4) (Fin 4) ℝ` |
| `Fin.sum_univ_succ` | `∑ i : Fin (n+1), f i = f 0 + ∑ i, f i.succ`; AddCommMonoid | Actually expanded a four-term sum into four additions. |
| `Finset.sum_comm` | Interchange of two finite sums in AddCommMonoid | Actually interchanged `∑ a : Fin 4, ∑ b : Fin 4, f a b`. |
| `Finset.sum_mul`, `Finset.mul_sum` | Distribution of finite sums over right/left multiplication | Expansion of contractions and quadratic terms |
| `Finset.sum_congr` | Equal index sets and termwise equality imply equal sums | Componentwise symmetry and inverse-matrix relations |
| `Matrix.mul_apply` | `(M * N) i k = ∑ j, M i j * N j k`; Fintype, Mul, AddCommMonoid | Actually checked the four-dimensional matrix-product component formula. |
| `Matrix.mulVec`, `Matrix.transpose` | Matrix action on column vectors and transpose | Underlying representation for raising/lowering and symmetry interfaces |
| `field_simp [hs]` | Actually removed denominators under s≠0, then used `nlinarith only [h]` to solve the linear relation | Division by s in the noncharacteristic case; retain the nonzero assumption. |
| `ring` | Actually proved the full three-term-square expansion over ℝ | Normalization of pointwise polynomial identities |

`ring` does not automatically handle unexpanded finite sums, matrix products, or unknown index permutations. First normalize with finite-sum APIs and symmetry/inverse relations, then treat scalar polynomials. The probe verifies availability of these operations, not the paper's Ricci or B identities.

The paper explicitly sums over all **ordered index pairs** (line 428). Direct double sums over Fin 4 × Fin 4 avoid losing off-diagonal multiplicity when replacing symmetric matrices by 10 independent components. Model the Lorentz bilinear pairing and auxiliary positive inner product separately.

Concrete import/cache limits found:

- `Matrix.IsSymm` is defined as Aᵀ=A at `Mathlib.LinearAlgebra.Matrix.Symmetric:29`; IsSymm.ext_iff gives its componentwise form. `Data.Matrix.Basic` **does not export** that name.
- Symmetric source exists, but its local `.olean` is missing. Direct import actually failed; the log is `AlgebraProbe.missing-symmetric-cache.log`. The explicit condition `∀ a b, k a b = k b a` is currently usable. Build the standard module in the project's independent dependency environment if adopting it.
- Initial probe name/simplification failures are retained in `AlgebraProbe.initial-failed.log`. The final pass is `AlgebraProbe.log`. Missing local cache must not be described as a missing library theorem.

## Medium-term navigation and missing bridges

Evidence levels are **execution-checked** (actual successful Lean `#check/#print` or example), **source-inspected** (pinned definitions, types, and context read but not compiled in this round's environment), **candidate** (related component without completed target-interface matching), and **not located by bounded search**. The latter three cannot be registered as completed paper dependencies.

### Finite Hermitian positivity

**Source-inspected:**

- `Mathlib.LinearAlgebra.Matrix.Hermitian:41`: `Matrix.IsHermitian A := Aᴴ = A`.
- `Mathlib.LinearAlgebra.Matrix.PosDef:47`: under `[Fintype n] [Ring R] [PartialOrder R] [StarRing R]`, `Matrix.PosSemidef M` is `M.IsHermitian ∧ ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x)`.
- In the same module, `:67`, `Matrix.PosSemidef.re_dotProduct_nonneg` gives nonnegativity of the quadratic form's real part under `[RCLike 𝕜]`. At `:71`, `conjTranspose_mul_mul_same` gives `A.PosSemidef → (Bᴴ * A * B).PosSemidef`.

Both local module `.olean` files were missing, so no Lean execution check ran. The pinned source uses `open scoped ComplexOrder` for complex nonnegativity. Retain the appropriate instances/scopes or use the real-part version when applying it. Finite complex covariance positivity can start here, but Gram-matrix transformations from coordinate covariance to fiber operators, Hermitian measure densities, and a.e. kernel constraints still require dedicated proofs. A matrix positive-semidefinite predicate is not the paper's positive Hermitian bundle-valued measure.

### Weak convergence, compactness, and lower semicontinuity

**Source-inspected:**

- `Mathlib.Topology.Algebra.Module.WeakDual:133,177` has `WeakSpace 𝕜 E` and linear equivalence `toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E`. They change the topology and cannot silently be treated as the original norm topology.
- `Mathlib.Analysis.LocallyConvex.WeakSpace:36`, `Convex.toWeakSpace_closure`: under real/complex scalars, suitable continuous operations, and real local convexity, the toWeakSpace image of a convex set's closure equals the weak closure of its image. Retain the contextual type hypotheses shown in the evidence excerpt.
- `Mathlib.Analysis.Normed.Module.WeakDual:254`, `WeakDual.isCompact_closedBall`: under `[ProperSpace 𝕜]`, a strong-dual closed ball corresponds to a compact subset of the weak-star dual. This concerns the **dual space**; application to the original L² space needs a representation/reflexivity bridge.
- `Mathlib.MeasureTheory.Measure.FiniteMeasure:679`, `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`: weak convergence of finite measures is equivalent to integral convergence for every `Ω →ᵇ ℝ`, requiring topology, measurable space, and measurable open sets.
- `Mathlib.MeasureTheory.Measure.Portmanteau:273`, `FiniteMeasure.limsup_measure_closed_le_of_tendsto`: under `[HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]`, a closed F satisfies limsup μᵢ(F)≤μ(F).

All these module caches were absent; the evidence is source inspection. Weak convergence of finite measures cannot directly replace vague convergence of locally finite Radon measures or extraction of a bundle-valued defect.

**Execution-checked:** `Mathlib.Topology.Algebra.Module.WeakBilin:104`, `WeakBilin.tendsto_iff_forall_eval_tendsto`: for a separating bilinear pairing B (requiring Function.Injective B), weak-topology convergence is equivalent to scalar-pairing convergence against every test vector. `WeakBilinProbe.lean` actually `#check`ed it with **exit 0**. The corresponding log and `WeakBilinProbe.result.json` contain the full type/result.

**Candidate bridge:** investigate weak lower semicontinuity of the norm through closed convex balls and Convex.toWeakSpace_closure. Searches for lowerSemicontinuous and norm/liminf in four specified weak-topology modules did not locate a directly applicable norm lower-semicontinuity declaration. This round neither proved the bridge nor inferred absence from all Mathlib.

### Radon properties, densities, and measures on manifolds

**Execution-checked:** `RegularMeasureProbe.lean` imports `Mathlib.MeasureTheory.Measure.Regular`; actual `#check/#print` **exit 0**.

- `MeasureTheory.Measure.Regular μ` includes finiteness on compact sets, outer regularity, and inner regularity of open sets by compact sets.
- `MeasureTheory.Measure.InnerRegular μ` additionally requires inner regularity of measurable sets by compact sets. The word “Radon” alone does not identify these concepts; the pinned source introduction explains two Radon conventions.
- The actual instance `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` requires `[PseudoMetrizableSpace X] [SigmaCompactSpace X] [BorelSpace X]` and local finiteness of μ. See the probe's full signature.

**Source-inspected/candidate:**

- `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym:56`, `Measure.withDensity_rnDeriv_eq (μ ν)`, requires `[HaveLebesgueDecomposition μ ν]` and μ≪ν, concluding `ν.withDensity (μ.rnDeriv ν) = μ`. This scalar-measure result does not directly imply positivity/measurability of matrix-valued densities.
- `Mathlib.MeasureTheory.VectorMeasure.Basic:57` provides `MeasureTheory.VectorMeasure`, a candidate underlying representation for finite-dimensional component measures. Its exact correspondence and transformation law for this paper's locally finite Hermitian bundle-valued measure are not yet established.
- `Mathlib.Geometry.Manifold.VectorBundle.Riemannian:238` has ContMDiffRiemannianMetric, and `Geometry.Manifold.Riemannian.Basic:77` has IsRiemannianManifold. The inspected content provides smooth inner-product/length structures. This round neither located nor constructed the required global positive density dV, coordinate-volume transformations, or bundle-valued measure interfaces on the cosphere bundle.

The latter three classes of modules lacked local cache. Covariance transformations between auxiliary metrics, coordinates, and fiber frames still need implementation; generic manifold/measure modules do not imply availability of the required interfaces.

### PDOs, Calderón estimates, and microlocal defects

**Source-inspected:** `Mathlib.Analysis.Distribution.FourierSchwartz:31` provides `SchwartzMap.fourierTransformCLM : 𝓢(V,E) →L[𝕜] 𝓢(V,E)` over a finite-dimensional real inner product space V, RCLike 𝕜, and compatible complex scalar actions. This is a relevant Fourier foundation; the module was not cached locally.

**Not located by bounded search:** searches within the three subtrees Analysis/Distribution, Analysis/Fourier, and Geometry/Manifold for `pseudodifferential`, `pseudo.differential`, `Calder[oó]n`, `microlocal`, `defect measure`, and `symbol calculus` did not find directly matching declarations. Scope and exit codes are in `bounded-search.log`. There was no unrestricted full-library search, and no claim that these theories are absent everywhere.

Actual consumers also require classical homogeneous order-zero symbols with IR regularization, operator bounds using finitely many symbol seminorms, local order −1 compactness, commutator orders/principal symbols, and extraction/localization of positive microlocal defects. Bridges from the existing Fourier/Schwartz components remain unverified. Keep them explicit unproved dependencies; hiding them in structure fields does not close them. This document gives neither an analysis-completion schedule nor a whole-library coverage guarantee.

## Recheck entry points

From the project root, run the following scripts. They write only their own audit directory and do not integrate project dependencies:

```powershell
& .\.project-verification\library-audit\source-identity.ps1
& .\.project-verification\library-audit\collect-evidence.ps1
& .\.project-verification\library-audit\run-probes.ps1 -Probe AlgebraProbe
& .\.project-verification\library-audit\run-probes.ps1 -Probe RegularMeasureProbe
& .\.project-verification\library-audit\run-probes.ps1 -Probe WeakBilinProbe
```

`.project-verification/` is ignored local evidence and does not travel with the repository. After independent dependency integration, verify actual imports/proofs in the project's own pinned dependency environment. Parent-workspace probe exit 0 cannot replace a project build or machine checking of paper results.
