# First consumer-based dependency audit and next gaps

[Chinese original](dependency-audit-round1.md)

2026-11-16; Lean 4.24.0, mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. This record uses the evidence levels of the [original audit](library-audit.en.md). Failure to locate an interface in a bounded search does not establish its absence from the library. This record approves no new mathematical assumption or extension of trust.

## Available consumable results

- The project's new CountableTests proves simultaneous convergence of a countable bounded family of real tests along the same strictly increasing subsequence. It closes only the countable-extraction step of F05, without constructing a positive defect measure.
- Actual L¹/Schwartz Fourier, modulation, and inversion interfaces in the pinned library were exercised by real probes and new proofs. The project also proved Schwartz Parseval using L¹ interchange of integrals and Schwartz inversion. See the [statement](../statements/initial-foundations.en.md) for the actual four-component off-cone energy and cutoff bridges.
- SchwartzMap.toLpCLM and L² approximation by continuous compactly supported functions were actually checked and instantiated on complex-valued `Lp 2 volume` over an arbitrary finite-dimensional real inner product space. No density axiom was added.

## Nearest remaining task: actual L² Fourier extension

An actual proof is needed of

```lean
DenseRange (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V))
```

Then use the proved Schwartz Parseval and inversion to extend Fourier isometrically to actual L² and prove agreement with the original Schwartz/L¹ Fourier transform. Taking DenseRange as an unproved parameter cannot justify calling this task complete.

The verified candidate chain is:

1. `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`: actual L² functions admit continuous compactly supported approximations, subject to its exact measure/topology hypotheses.
2. `UniformContinuous.exists_contDiff_dist_le`: uniform smooth approximation on the whole space. This module was inspected at source level only in this round; missing cache was not treated as absence of the theorem.
3. For a fixed continuous compactly supported function, select a fixed smooth compact cutoff equal to 1 on its support. Multiply the approximation in step 2 by that cutoff, retaining compact support and controlling the L² error by fixed support volume and uniform error.
4. Use `HasCompactSupport.toSchwartzMap` to reach the actual Schwartz→L² map. Combine the two approximation stages to prove density, then perform the isometric extension.

The compactly supported smooth L² error bridge in step 3 still requires actual implementation; exact library matching remains under investigation. Ordinary uniform smooth approximation does not itself ensure compact support, so this stage cannot be skipped. Actual frequency-symbol multiplication, inverse transform, sharp/smooth operators, measurability, zero frequency a.e., and whole-space tails are also needed before closing the parent target at original line 3193.

## Existing F05 components and concrete missing bridges

| Component and evidence | What it supplies | What remains |
| --- | --- | --- |
| RealRMK.rieszMeasure / integral_rieszMeasure; source inspected | Measure representation of an already constructed positive real C_c functional | Actual PDO test limits, positivity, extension to C_c, locally finite Hermitian bundle-valued densities and transformations |
| VectorMeasure.withDensityᵥ; source inspected | Vector measure from a globally integrable density | **This definition returns zero when the density is not globally Integrable.** Locally finite full-bundle cases need separate compact exhaustion and compatibility; direct application is insufficient. |
| Matrix.PosSemidef and congruence transformations; source inspected | Finite-dimensional density positivity and preservation of positivity under congruence | Actual bridges from system integral constraints to a.e. `A M Aᴴ=0`, then to `range M⊆ker A` |
| WeakDual.isCompact_closedBall; source inspected | Weak-star compactness of a dual closed ball | Not a sequential compactness interface. This round's countable extraction avoids that jump, but density/uniform continuity for all symbols still needs proof. |
| IsCompactOperator; source inspected | Consequences for operators already proved compact | Does not automatically identify a local order −1 symbol with a compact operator, or prove weak-zero to strong-zero behavior. |

No directly matching F05 positive bundle-valued microlocal extraction/localization interface was located in the terminology search restricted to Fourier, Distribution, Operator, InnerProductSpace, and related geometry/vector-measure paths. Exact library matching remains pending. The applicable signature of a precise literature version was not verified in this round either.

## Keep A01 and P01 separate

A01 needs actual first-order PDO commutator control with a Lipschitz scalar and its energy application. P01 needs a gradient-type Calderón norm bound for fixed whole-space IR-regularized `Π∂b`, depending only on `‖∂f‖∞`, without requiring the entire f to be globally bounded. The opNorm definition of a generic CLM cannot substitute for either result or identify them with one another.

The exact identity used later by P01 is

```text
[Π,f]∂b w = [Π∂b,f]w − Π((∂b f)w).
```

Current Lp domination estimates and CLM operator-norm interfaces apply only to actual constructed elements/maps; they do not supply this Calderón estimate. No directly matching PDO/commutator declaration was found within the bounded search. Keep the issue pending rather than starting an unbounded “rewrite the entire theory.”

Source identities, bounded search parameters, actual-type probes, and their separate exit codes are saved in workspace N1/N3 evidence. Candidate new sources have separate fixed bindings and actual machine checks. The updated scope inventory only added X02 as an EXT-HARMONIC consumer; it added no duplicate parent target or inter-slice edge.
