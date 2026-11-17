# The two F05 extensions and the next interface

[Chinese original](dependency-audit-round2.md)

2026-11-16; Lean 4.24.0, mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. This record refines the next task from the first audit without enlarging the paper's assumptions, trust, or certification scope.

## General tools implemented

`Burnett.Analysis.Compactness.DenseTests` constructs a unique continuous linear pointwise limit L on the whole space from a sequence of actual continuous linear functionals uₙ, an explicit uniform operator-norm bound, and convergence on a dense test set, retaining the same norm bound. It does not require completeness of the test space and does not give operator-norm convergence. A separate tool preserves nonnegativity in the actual limit when the nonnegative lower-bound error tends to zero.

This general theorem does not establish those premises for the original PDO family. In particular, control of finitely many symbol derivatives cannot be replaced directly by C⁰/sup-norm control of the symbol. Putting test-family density and an unestablished norm bound into a structure does not complete defect extraction.

## Complete the two extensions separately

1. Along the same common subsequence, use an actual order-zero operator bound in finitely many symbol seminorms to extend limits on countably many dense smooth tests to all smooth symbols in the original defect-test class. Actual quantification, base support, and uniform estimates are required.
2. For nonnegative symbols, derive positivity of the limit through an actual square decomposition/Gårding-type vanishing error. Then use a positive order-unit cutoff on a fixed support to obtain C⁰ control. Extend to the entire actual C_c space through smooth approximation preserving a common support, checking linearity, positivity, independence, and local compatibility.

The bound in step 2 does not follow merely from the finite-order seminorm bound in step 1. Both steps retain the same subsequence and all angular tests. The correspondence between real parts and self-adjoint representatives, compact lower-order remainders, and conjugation conventions in the tests must be proved explicitly.

## Exact available RMK interface

The pinned library's `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real` supplies `RealRMK.rieszMeasure` and `RealRMK.integral_rieszMeasure`, taking an actual positive real linear functional on the entire space, `C_c(X,ℝ) →ₚ[ℝ] ℝ`. The interface does not first assume finite total mass or require continuity as an extra input. Check the concrete topology, Borel, and regularity instances when actually applying it.

RMK itself and related C_c/PositiveLinearMap modules lacked built caches in this round, so they received **source inspection only**, not a recorded successful Lean invocation. With existing Content, Urysohn, and SmoothApprox dependencies, 13 APIs and corresponding instances for regularity, finiteness on compact sets/local finiteness, inner regularity on all Borel sets under sigma-compactness, and fixed nested cutoffs were actually checked. Missing cache does not mean a library theorem is missing. Prepare pinned-version cache and invoke the APIs when a later consumer needs them.

The nearest implementation task is local C⁰ control of a positive functional on fixed support and a positive linear extension preserving common support. Actual PDO boundedness, Gårding error, compactness of order −1 remainders, global bundle-valued measures, Gram covariance conversion, and a.e. system-kernel localization all remain open. General dense extension, an RMK interface, or a positive-semidefinite kernel lemma supplies only individual inputs to these consumers; none closes F05 alone.
