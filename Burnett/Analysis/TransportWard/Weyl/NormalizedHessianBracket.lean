import Burnett.Analysis.TransportWard.Weyl.NormalizedHessianSymbol
import Burnett.Analysis.TransportWard.Weyl.ActualChartPhase

/-! The principal matrix of the normalized Euler density on the actual
phase-space Ricci kernel. -/

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.V03.Palatini

open Set Bundle Burnett.RicciSymbol Burnett.Geometry Burnett.V02
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear UnitNullCompactness
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open scoped ContDiff Manifold

local notation "E" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- At a true nonzero cotangent point the Poisson derivative of the
orthonormal Euler principal form has the required mixed null-kernel value
and zero off-null compression. The lower fields are held fixed. -/
theorem normalizedDensityEulerPrincipalForm_bracket_actualChart_RicciKernel
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E c).source)
    (hξ : cotangentCoords c p ≠ 0) (u v : I → ℂ)
    (hU : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E c p.proj, cotangentCoords c p))
      (cotangentCoords c p) (assembleComplexMetricComponents orthonormalMetricDirection u) i j = 0)
    (hV : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E c p.proj, cotangentCoords c p))
      (cotangentCoords c p) (assembleComplexMetricComponents orthonormalMetricDirection v) i j = 0)
    (a : E → Covector → ℝ) :
    let g := chartLowerMetric B c
    let z : Phase := (chartAt E c p.proj, cotangentCoords c p)
    let J := assembleComplexMetricComponents orthonormalMetricDirection u
    let L := assembleComplexMetricComponents orthonormalMetricDirection v
    fderiv ℝ (fun y : Phase => densityEulerPrincipalForm
      orthonormalMetricDirection (g y.1) y.2 u v) z (phasePoissonDirection a z) =
        if dualEnergy B hSig.isNondegenerate p = 0 then
          4 * (phaseDensity g z : ℂ) * (canonicalBracket (coordinateHamiltonian g) a z.1 z.2 : ℂ) *
            physicalForm (phaseInverse g z) J L
        else 0 := by
  intro g z J L
  let e := chartAt E c
  have hz : z.1 ∈ e.target := e.mapsTo hp
  obtain ⟨hG, hDet, hSym⟩ := chartLowerMetric_phase_inputs B hB hSig.isNondegenerate hSig.isSymmetric c
  obtain ⟨hInv, hw⟩ := differentiableAt_phaseInverse_density g e.target e.open_target hG hDet z hz
  have hJ : IsSymmetricComplexTensor J := assembleComplexMetricComponents_isSymmetric
    orthonormalMetricDirection orthonormalMetricDirection_isSymmetric u
  have hL : IsSymmetricComplexTensor L := assembleComplexMetricComponents_isSymmetric
    orthonormalMetricDirection orthonormalMetricDirection_isSymmetric v
  have hEq : (fun y : Phase => densityEulerPrincipalForm orthonormalMetricDirection (g y.1) y.2 u v) =
      fun y => hermitianPrincipalHessianPairing (g y.1) y.2 J L :=
    funext fun y => densityEulerPrincipalForm_eq_hermitianFourierHessian
      orthonormalMetricDirection (g y.1) y.2 u v
  rw [hEq, ← fderiv_phaseHessianPairing_eq_fderiv_hermitianPrincipalHessianPairing
    g e.target e.open_target hSym z hz J L hJ hL,
    ← phaseEinsteinPoissonBracket_ordered_pairing g z hInv hw J L a]
  exact phaseEinsteinPoissonBracket_actualChart_RicciKernel B hB hSig c p hp hξ J L hL hU hV a

end Burnett.V03.Palatini
