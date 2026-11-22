# Fourier action of the fixed gauge-complement projection

[简体中文](gauge-projection-fourier-action.zh-CN.md)

This delivery corresponds to lines 1619–1642, 1697, and 2036–2042 of the locked manuscript and uses the same fixed infrared cutoff throughout.

- Each entry of the matrix symbol defines a continuous complex linear Fourier multiplier on Schwartz space. Its radian Fourier transform and physical-space integral agree with the original symbol.
- The pointwise complex matrix action is the double sum of those components and annihilates pure-gauge amplitudes at every frequency. The radian derivative formula gives the frequency cancellation for the symmetric gradient of a Schwartz covector.
- Acting on the continuous complex linear dual of Schwartz space, the componentwise projection annihilates the symmetric gradient of every tempered covector. The pairing uses precomposition. The identification of the manuscript's compactly supported chart distributions with this dual model is a separate application.
- For each fixed component and each finite real $p>1$, the regularized multiplier satisfies an $L^p$ bound on scalar Schwartz inputs. The proof checks the radian symbol of one fixed high-pass operation followed by the homogeneous multiplier.

The full `prop:general-projection` still requires the projected fields and their norm bounds for the original sequence, the bounded whole-space divergence source, and preservation of the full angular measure. Author confirmation is pending.

- `Burnett.A07.radianFourier_coordinateDerivative`
- `Burnett.P01.gaugeProjectionSchwartzComponent_radianFourier`
- `Burnett.P01.gaugeProjectionSchwartzComponent_eq_radianAction`
- `Burnett.P01.regularizedComplexGaugeProjection_apply`
- `Burnett.P01.regularizedComplexGaugeProjection_kills`
- `Burnett.P01.regularizedComplexGaugeProjection_symmetrizedGradient`
- `Burnett.P01.temperedGaugeProjection_symmetrizedGradient`
- `Burnett.P01.radianFourier_projectionInfraredAction`
- `Burnett.P01.radianAction_regularizedGaugeProjectionSymbol`
- `Burnett.P01.exists_regularizedGaugeProjectionSymbol_Schwartz_Lp_bound`

[Shared source bindings](gauge-projection-fourier-action-source-bindings.json)
