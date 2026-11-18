# Local weighted disintegration

[简体中文](local-disintegration.zh-CN.md)

This package supports the proof of the base marginal and angular disintegration corollary in manuscript lines 487–518. The two source modules were checked in isolation against base commit `be653f49507fbd73a2f466cb308b3f65dd30de0e`.

`Burnett.Analysis.BaseMarginal.SmoothTests` proves two local facts. Let a real field be continuous on an open coordinate region, and suppose the measure gives positive mass to each nonempty open subset of that region. Assume the product of the field with every smooth real test compactly supported in the region is integrable. If the product has nonnegative integral for every nonnegative such test, then the field is pointwise nonnegative there. Two finite measures concentrated on the same open coordinate region agree when they have the same integrals against all compact smooth tests supported there.

`Burnett.Analysis.BaseMarginal.FiberKernel` starts from a finite positive measure ρ on a coordinate product and a finite base measure dV. Its hypothesis is the marginal identity `ρ.fst = dV.withDensity w` for a supplied measurable weight w with values in the extended nonnegative reals and a bound `w(y) ≤ C < ∞`. It also requires the joint measure to be concentrated on a measurable relation Z. The combination theorem constructs one weighted conditional kernel κ for all its conclusions.

- `dV ⊗ₘ κ = ρ`.
- The fiber measure `κ y` is finite and `κ y univ = w y` at every coordinate base point.
- The real fiber mass is integrable over dV. The integral of the extended nonnegative fiber mass is `ρ univ`.
- For dV-almost every y, the fiber measure is concentrated on `{η | (y, η) ∈ Z}`.
- Every other finite kernel producing the same joint measure over dV is dV-almost everywhere equal to κ. Here the Lean class `IsFiniteKernel` provides a uniform finite bound on the fiber masses.

The inherited proofs come from the independently reviewed local package. The uniqueness theorem now spells the Euclidean coordinate space as `CoordinateSpace`, the definitionally equal coordinate alias used by the other kernel results. The new combination theorem takes the known marginal identity as a hypothesis. The actual marginal from the original metric, its almost-everywhere Einstein moments, and global assembly remain obligations of F08.

## Registered support targets

| Claim ID | Module suffix | Declaration suffix |
| --- | --- | --- |
| `base-marginal:smooth-test-positivity` | `SmoothTests` | `nonnegOn_of_smooth_test_integrals` |
| `base-marginal:smooth-test-measure-ext` | `SmoothTests` | `finiteMeasures_eq_of_local_smooth_tests` |
| `base-marginal:finite-kernel-unique` | `FiberKernel` | `localFiberKernel_unique` |
| `base-marginal:local-weighted-disintegration` | `FiberKernel` | `exists_localFiberDisintegration` |

All modules use the `Burnett.Analysis.BaseMarginal` prefix and all declarations use `Burnett.F08.ActualBaseMarginal`. These claims support `cor:base-marginal`.


The isolated Lean replay checked 14 declarations using only the policy A axioms. The [source bindings](local-disintegration-source-bindings.json) identify the checked inputs.
