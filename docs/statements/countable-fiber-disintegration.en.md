# Disintegration over a countable cover

[简体中文](countable-fiber-disintegration.zh-CN.md)

The proof of Corollary `cor:base-marginal` constructs angular measures on an exhaustion, multiplies their conditional probabilities by the base density, and asserts almost-everywhere uniqueness for a fixed physical measure. The three Lean modules implement this measure-theoretic step for measurable spaces `X,Y`. The relevant manuscript passages are lines 494–502 and 511–515.

| Declaration in `Burnett.F08.FiberGluing` | Mathematical statement |
| --- | --- |
| `localFiberKernel_unique_of_integral_sections` | On a finite base, a finite kernel and a competing measurable kernel that gives the same integrals on every measurable joint set agree almost everywhere as measures. The base type is countable or the fiber σ-algebra is countably generated. |
| `patchKernel_disintegrates` | Finite kernels representing restrictions of one joint measure on a countable measurable cover paste to a kernel representing the joint measure. Every fiber is finite. Each patch may have its own bound. |
| `patchKernel_unique_of_integral_sections` | If the base measure is finite on each patch, any measurable kernel representing all measurable sets of this joint measure agrees almost everywhere with the pasted kernel, under the same countability hypothesis as the local uniqueness theorem. |
| `exists_weighted_disintegration_on_cover` | A prescribed first marginal and concentration on a measurable relation yield a single s-finite kernel over the original base measure, with the mass, concentration, and uniqueness described below. |

For the last theorem, `v` is an s-finite base measure, `Y` is a nonempty standard Borel space, and the positive joint measure `ρ` has first marginal `v.withDensity w`. The nonnegative extended-real weight `w` is measurable and bounded by a finite constant on each member of a countable measurable cover. The restrictions of the base measure and joint measure over each patch are finite. The joint measure gives zero mass to the complement of the measurable relation `Z`.

The assembled kernel `k` satisfies `v ⊗ₘ k = ρ`. For every base point `x`, its fiber is a finite measure of mass exactly `w x`, hence zero wherever `w x = 0`. For almost every `x`, this fiber gives zero mass to the complement of the section of `Z` at `x`. Any measurable kernel satisfying the section-integral representation of the **same** joint measure on every measurable joint set equals `k` as a measure-valued function outside one base-null set. This competitor requires no finiteness assumption. The selected representative has the stated mass at every point, including the exceptional set in the uniqueness conclusion.

Only the weighted existence theorem assumes a nonempty standard Borel fiber. Pasting itself uses arbitrary measurable spaces and s-finite base measure. Equality of the reconstructed measure follows from the common local joint restrictions, even when their finite bounds grow along the cover. The auxiliary theorem `patchKernel_ae_of_local` also passes any almost-everywhere fiber property on those patches to the global kernel.

These are four supporting targets of slice F08. The geometric application still has to supply the intrinsic phase and projection, `π_* μ = e_r dV`, local finiteness and local bounds, concentration on the unit null shell, and the stress-tensor moment law. The parent corollary remains open at this stage. An independent mathematical readback and human semantic confirmation are pending.

The library reaches the three modules through `Burnett.Analysis.FiberDisintegration.Weighted`. An isolated build compiled them using Lean 4.24.0 and the locked mathlib dependencies of the recorded baseline. All ten public declarations passed the axiom audit. [Source bindings](countable-fiber-disintegration-source-bindings.json)
