import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectionInfraredDifference

/-! The homogeneous projected derivative is the weak derivative of the actual projected field. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.P01

open MeasureTheory Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau radianFourier_scaled)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ComplexConjugate FourierTransform InnerProduct

/-- The actual homogeneous coordinate projection of one tensor component. -/
def homogeneousProjectionComponent (w : ProjectionSchwartzMatrix) (k : OrderedPair) : ComplexL2 E :=
  ∑ i : OrderedPair, fourierMultiplier (principalProjectionComponentSymbol k.1 k.2 i.1 i.2)
    ((w i.1 i.2).toLp 2 volume)

private theorem inner_derivative_fourierMultiplier (m : BoundedSymbol E) (f w : SchwartzMap E ℂ) (d : Fin 4) :
    inner ℂ ((coordinateDerivative d f).toLp 2 volume) (fourierMultiplier m (w.toLp 2 volume)) =
      - inner ℂ (f.toLp 2 volume) (fourierMultiplier m ((coordinateDerivative d w).toLp 2 volume)) := by
  rw [← (fourierL2Equiv (V := E)).inner_map_map ((coordinateDerivative d f).toLp 2 volume)
    (fourierMultiplier m (w.toLp 2 volume)),
    ← (fourierL2Equiv (V := E)).inner_map_map (f.toLp 2 volume)
      (fourierMultiplier m ((coordinateDerivative d w).toLp 2 volume)),
    fourier_fourierMultiplier, fourier_fourierMultiplier, L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [fourierL2Equiv_schwartz_ae f, fourierL2Equiv_schwartz_ae w,
    fourierL2Equiv_schwartz_ae (coordinateDerivative d f), fourierL2Equiv_schwartz_ae (coordinateDerivative d w),
    symbolL2_ae m (fourierL2Equiv (w.toLp 2 volume)),
    symbolL2_ae m (fourierL2Equiv ((coordinateDerivative d w).toLp 2 volume))] with ξ hf hw hdf hdw hm hm'
  rw [hdf, hm, hm', hf, hw, hdw, RCLike.inner_apply', RCLike.inner_apply']
  have eF := radianFourier_coordinateDerivative d f (tau • ξ)
  have eW := radianFourier_coordinateDerivative d w (tau • ξ)
  simp only [radianFourier_scaled] at eF eW
  change conj (𝓕 (coordinateDerivative d f : E → ℂ) ξ) * (m ξ * 𝓕 (w : E → ℂ) ξ) =
    -(conj (𝓕 (f : E → ℂ) ξ) * (m ξ * 𝓕 (coordinateDerivative d w : E → ℂ) ξ))
  rw [eF, eW]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Testing the actual homogeneous projected field against a Schwartz
derivative gives the weak derivative represented by the previously checked
projected coordinate derivative. In particular this applies to every
smooth compactly supported complex test. -/
theorem homogeneousProjectionComponent_weakCoordinateDerivative
    (w : ProjectionSchwartzMatrix) (d : Fin 4) (k : OrderedPair) (f : SchwartzMap E ℂ) :
    inner ℂ ((coordinateDerivative d f).toLp 2 volume) (homogeneousProjectionComponent w k) =
      - inner ℂ (f.toLp 2 volume) (homogeneousProjectedCoordinateDerivative w d k) := by
  simp only [homogeneousProjectionComponent, homogeneousProjectedCoordinateDerivative, inner_sum,
    inner_derivative_fourierMultiplier, Finset.sum_neg_distrib]

end Burnett.P01
