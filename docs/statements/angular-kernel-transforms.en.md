# Coordinate changes and weights for angular kernels

[简体中文](angular-kernel-transforms.zh-CN.md)

The paper compares physical measures under a change of auxiliary unit shell, then expresses a phase measure through its conditional angular laws. These supporting results transport a given disintegration through a measurable change of coordinates or a nonnegative weight. The geometric applications correspond to lines 481–485 and 494–515 of the locked manuscript.

| Lean declaration | Result |
| --- | --- |
| `coordKernel_integral_sections` | Let k be an s-finite kernel over an s-finite base volume. Change the base by b, read k at a measurable inverse, and push each angular measure through φ. If the inverse recovers the original base point almost everywhere, integration of the resulting sections computes the image of the original joint measure on every measurable joint event. |
| `coordKernel_real_moment` | The real Bochner integral of a measurable test against the coordinate kernel is the integral of its pullback against the original conditional measure. Physical second-moment integrability and identification with the Einstein tensor require further estimates. |
| `reweightedKernel_apply` | At every base point the transformed kernel is the image under F of the original conditional measure with measurable nonnegative weight w. |
| `reweightedKernel_reconstruct` | Suppose that on every measurable set the original measure μ is the integral of an s-finite kernel against a base measure. The transformed kernel reconstructs the image of wμ under F on every measurable target event, including events with infinite mass. |

In the application to a new auxiliary metric, F divides a covector by its new norm and w is that norm squared. This package supplies the measure operations. The original vacuum sequence, geometric choice of maps and identification of its angular measure belong to the consuming geometric proofs. The parent corollary remains open in this repository snapshot. Author confirmation is pending. [Source bindings](angular-kernel-transforms-source-bindings.json)
