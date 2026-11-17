# The first real-algebra fragment of the Ricci symbol

Source: `paper/burnett.tex`, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. This fragment covers415–418,432–436,452 and supplies local algebra for the quadratic-measure construction.

## Mathematical meaning

Fix real four-dimensional coordinates at a point with indices `Fin 4`. Write `gInv` for inverse-metric components, `ξ` for a covector, and `k` for covariant two-tensor components. Every repeated index is summed over all ordered indices.

$$
s=\sum_{a,b}g^{ab}\xi_a\xi_b,\qquad
t=\sum_{a,b}g^{ab}k_{ab},\qquad
q_b=\sum_a\xi^a k_{ab}.
$$

The code defines raising, those three contractions, and

$$
\mathcal R_\xi(k)_{ab}
=\tfrac12(sk_{ab}+\xi_a\xi_b t-\xi_aq_b-\xi_bq_a).
$$

If `s ≠ 0` and every component of `𝓡ξ(k)` vanishes, take

$$v_b=\frac{q_b-t\xi_b/2}{s}$$

Then `k_ab = ξ_a v_b + v_a ξ_b`. Continue with the original definition

$$
c(k)^a{}_{bc}=\tfrac12(\xi_b k_c{}^a+\xi_c k_b{}^a-\xi^a k_{bc}),
$$

$$
B_{bc}(k,k)=\sum_{a,e}
\left(c(k)^a{}_{ce}c(k)^e{}_{ba}-c(k)^a{}_{ae}c(k)^e{}_{bc}\right).
$$

For a pure-gauge tensor, `c(k)^a_bc = ξ_b ξ_c v^a`; both terms cancel at each `(a,e)`, hence `B_bc(k,k)=0`. Thus the real diagonal quadratic term vanishes on the noncharacteristic Ricci-symbol kernel.

The implementation actually allows arbitrary real `gInv`/`k`, without assumed symmetry or Lorentz signature: this one-way result holds on that larger domain. Actual inverse Lorentz-metric components and original symmetric k instantiate it. No Euclidean identity replaces the inverse metric, and the full manifold-metric inversion interface is not implemented.

## Actual declarations and source

Module: [RicciSymbol.lean](../../Burnett/Algebra/RicciSymbol.lean), namespace `Burnett.RicciSymbol`.

| Manifest subitem | Actual theorem | Mathematical role | Source location |
| --- | --- | --- | --- |
| `ricci:kernel-pure-gauge` | `kernel_eq_pureGauge` | Construct an explicit gauge vector in the noncharacteristic kernel | 415–418,452 |
| `ricci:raise-pure-gauge` | `raiseSecond_pureGauge` | Linear expansion of raising a pure-gauge tensor | Proof step at434,452 |
| `ricci:connection-pure-gauge` | `connectionSymbol_pureGauge` | Connection principal symbol equals `ξ_b ξ_c v^a` | 434,452 |
| `ricci:quadratic-pure-gauge` | `quadraticSymbol_pureGauge` | Full ordered quadratic contraction of a pure-gauge tensor vanishes | 435,452 |
| `ricci:quadratic-kernel` | `quadraticSymbol_eq_zero_of_noncharacteristic_kernel` | Combine kernel representation with quadratic elimination | 452 |

These subitems belong to existing `unnum:quadratic-symbol-algebra`; the full432–465 passage is not marked complete. Exact types below are quoted literally from the current implementation, with full definitions in the module. Target auditing retains actual type/axiom/source checks.

## Current evidence and boundaries

Fixed Lean4.24.0, Mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Implementer and independent reviewer actually compiled and queried types/axioms in read-only library probes after checking versions. The five theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The project's independent dependencies and target audit also actually passed; CI is recorded separately for actual fixed commits, not inferred from local probes.

The [independent mathematical readback/comparison](ricci-symbol-review.en.md) starts from actual code/types, then checks the source. Author confirmation follows actual replies; nonexistent confirmation is not filled in.

Not covered: full quadratic expansion at447–448, mixed/Hermitian polarization, null branch `s=0`, gauge-quotient nonnegativity, defect measures, transport, or the main theorem. No claim is made that pure-gauge tensors conversely lie in the Ricci kernel for arbitrary nonsymmetric `gInv`.

## Verbatim current Lean types

```lean
theorem kernel_eq_pureGauge (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    k = pureGauge ξ (kernelGaugeVector gInv ξ k)
```

```lean
theorem raiseSecond_pureGauge (gInv : Tensor2) (ξ v : Covector) (c a : Index) :
    raiseSecond gInv (pureGauge ξ v) c a =
      ξ c * raiseCovector gInv v a + v c * raiseCovector gInv ξ a
```

```lean
theorem connectionSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (a b c : Index) :
    connectionSymbol gInv ξ (pureGauge ξ v) a b c =
      ξ b * ξ c * raiseCovector gInv v a
```

```lean
theorem quadraticSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (b c : Index) :
    quadraticSymbol gInv ξ (pureGauge ξ v) b c = 0
```

```lean
theorem quadraticSymbol_eq_zero_of_noncharacteristic_kernel
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (b c : Index) : quadraticSymbol gInv ξ k b c = 0
```
