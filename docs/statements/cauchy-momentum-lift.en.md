# Full momentum from a smooth spacelike Cauchy slice

This proof corresponds to lines 2989–3045 of Lemma 6.1, `lem:lift`. The cotangent model uses a Hausdorff, second-countable smooth manifold. A smooth Lorentz metric, a positive auxiliary metric, a smooth spacelike slice, and its crossing law for regular causal curves provide the geometric inputs. The lift uses the same unit-null measure as `HasActualUnitTransport`.

`Burnett.Geometry.CotangentHamiltonInitialFamily.exists_actualFullMomentumLift_of_smooth_spacelike_cauchy` constructs the energy from the unique transverse hit of the actual maximal Hamilton trajectory. The energy is smooth on the punctured null cone, positively homogeneous of degree one, and invariant along the flow. The proof allows finite affine endpoints and noncompact slices.

The scale on the unit-null bundle is the reciprocal of the auxiliary covector norm at the hit. Its weighted pushforward is Radon, has punctured null-cone support, and preserves the second moment on every compact base set. It also preserves the pairing and integrability of quadratic observables. Every smooth compactly supported full-cotangent test has an integrable Hamilton derivative with integral zero.

Deriving a smooth spacelike Cauchy slice from global hyperbolicity remains a proof obligation. The main theorem also needs this lift applied to the ray measure shared by the quadratic theorem and variational transport.
