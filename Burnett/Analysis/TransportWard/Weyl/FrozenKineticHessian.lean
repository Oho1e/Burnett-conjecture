import Burnett.Analysis.TransportWard.Weyl.FrozenKineticTrace
import Burnett.Analysis.TransportWard.Weyl.CoordinatePhase
import Burnett.Analysis.TransportWard.Amplitude

/-! The actual frozen Fourier ΓΓ coefficient and the ordered complex pairing. -/

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V02

open Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference (CoordinateSpace christoffel)
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ComplexConjugate Topology

private theorem gammaCross_planes_eq_neg_trace_cross (B : Mat) (p : Covector) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    gammaCross B (planeJet p J) (planeJet p L) =
      -metricTrace B (connectionCrossSymbol B p J L) := by
  have h (i j : Index) :
      connectionCross (christoffel B (planeJet p J)) (christoffel B (planeJet p L)) i j =
        -connectionCrossSymbol B p J L i j := by
    simp only [connectionCross, christoffel_plane B p J hJ, christoffel_plane B p L hL,
      connectionCrossSymbol, ← Finset.sum_neg_distrib, neg_sub]
  simp only [gammaCross, metricTrace, h, mul_neg, Finset.sum_neg_distrib]

/-- The signed opposite-frequency Fourier pairing uses exactly the original
ΓΓ coefficient, and the mixed product from F06 enters with multiplier `-2w`. -/
theorem principalHessianPairing_eq_neg_two_trace_mixed (G : Mat) (p : Covector) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalHessianPairing G p J L =
      -2 * metricDensity G * metricTrace (inverseMatrix G)
        (mixedQuadraticSymbol (inverseMatrix G) p J L) := by
  let B := inverseMatrix G
  have hNeg : planeJet (-p) L = (-1 : ℝ) • planeJet p L := by
    simpa only [neg_one_smul] using planeJet_smul_covector p L (-1 : ℝ)
  have hTrace : metricTrace B (connectionCrossSymbol B p J L) +
      metricTrace B (connectionCrossSymbol B p L J) =
        2 * metricTrace B (mixedQuadraticSymbol B p J L) := by
    simp only [metricTrace, mixedQuadraticSymbol, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change -(metricDensity G * kineticCoefficient B (planeJet p J) (planeJet (-p) L)) =
    -2 * metricDensity G * metricTrace B (mixedQuadraticSymbol B p J L)
  rw [hNeg, kineticCoefficient_smul_right, kineticCoefficient_eq_cross,
    gammaCross_planes_eq_neg_trace_cross B p J L hJ hL, gammaCross_planes_eq_neg_trace_cross B p L J hL hJ]
  linear_combination -(metricDensity G) * hTrace

private theorem inverseMatrix_symmetric (G : Mat) (hG : IsSymmetricTensor G) :
    IsSymmetricTensor (inverseMatrix G) :=
  phaseInverse_symmetric (fun _ => G) ((0 : CoordinateSpace), (0 : Covector)) hG

/-- General-metric version of the real flat-background Fourier Hessian
identification. Both sides use the original signed ΓΓ and Ricci coefficients. -/
theorem principalHessianPairing_eq_physicalRicci (G : Mat) (p : Covector) (J L : Mat)
    (hG : IsSymmetricTensor G) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalHessianPairing G p J L = metricDensity G *
      physicalPairing (inverseMatrix G) (ricciSymbol (inverseMatrix G) p J) L := by
  rw [principalHessianPairing_eq_neg_two_trace_mixed G p J L hJ hL,
    physicalRicci_eq_neg_two_trace_mixedQuadraticSymbol (inverseMatrix G) p J L
      (inverseMatrix_symmetric G hG) hJ hL]
  ring

/-- Hermitian extension of the actual real kinetic Hessian, linear in the
first amplitude and conjugate-linear in the second. -/
def hermitianPrincipalHessianPairing (G : Mat) (p : Covector) (J L : ComplexTensor2) : ℂ :=
  ⟨principalHessianPairing G p (tensorRe J) (tensorRe L) +
    principalHessianPairing G p (tensorIm J) (tensorIm L),
    principalHessianPairing G p (tensorIm J) (tensorRe L) -
    principalHessianPairing G p (tensorRe J) (tensorIm L)⟩

/-- Exact equality of the Fourier ΓΓ Hessian and the weighted raised Ricci
pairing on both complex slots, including the imaginary mixed terms. -/
theorem hermitianPrincipalHessianPairing_eq_hessianPairing (G : Mat) (p : Covector)
    (J L : ComplexTensor2) (hG : IsSymmetricTensor G) (hJ : IsSymmetricComplexTensor J)
    (hL : IsSymmetricComplexTensor L) :
    hermitianPrincipalHessianPairing G p J L =
      hessianPairing (inverseMatrix G) (metricDensity G) p J L := by
  let B := inverseMatrix G
  have hr : tensorRe (complexRicciSymbol B p J) = ricciSymbol B p (tensorRe J) :=
    funext fun i => funext fun j => complexRicciSymbol_re B p J i j
  have hi : tensorIm (complexRicciSymbol B p J) = ricciSymbol B p (tensorIm J) :=
    funext fun i => funext fun j => complexRicciSymbol_im B p J i j
  have hJr := tensorRe_symmetric J hJ
  have hJi := tensorIm_symmetric J hJ
  have hLr := tensorRe_symmetric L hL
  have hLi := tensorIm_symmetric L hL
  change hermitianPrincipalHessianPairing G p J L = hessianPairing B (metricDensity G) p J L
  rw [hessianPairing_eq_physicalRicci B (inverseMatrix_symmetric G hG)]
  unfold hermitianPrincipalHessianPairing
  rw [principalHessianPairing_eq_physicalRicci G p _ _ hG hJr hLr,
    principalHessianPairing_eq_physicalRicci G p _ _ hG hJi hLi,
    principalHessianPairing_eq_physicalRicci G p _ _ hG hJi hLr,
    principalHessianPairing_eq_physicalRicci G p _ _ hG hJr hLi]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hermitianPhysicalPairing_re, hr, hi]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hermitianPhysicalPairing_im, hr, hi]
    ring

/-- In the varying background, the previous frozen identity holds pointwise
for the same phase symbol differentiated in the Ricci-kernel compression. -/
theorem phaseHessianPairing_eq_hermitianPrincipalHessianPairing
    (g : CoordinateSpace → Mat) (z : Phase) (hG : IsSymmetricTensor (g z.1))
    (J L : ComplexTensor2) (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L) :
    phaseHessianPairing g J L z = hermitianPrincipalHessianPairing (g z.1) z.2 J L :=
  (hermitianPrincipalHessianPairing_eq_hessianPairing (g z.1) z.2 J L hG hJ hL).symm

/-- On a symmetric coordinate neighborhood the frozen identification
also identifies the derivative used in the actual Poisson bracket. -/
theorem fderiv_phaseHessianPairing_eq_fderiv_hermitianPrincipalHessianPairing
    (g : CoordinateSpace → Mat) (U : Set CoordinateSpace) (hU : IsOpen U)
    (hG : ∀ x ∈ U, IsSymmetricTensor (g x)) (z : Phase) (hz : z.1 ∈ U)
    (J L : ComplexTensor2) (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L) :
    fderiv ℝ (phaseHessianPairing g J L) z =
      fderiv ℝ (fun y : Phase => hermitianPrincipalHessianPairing (g y.1) y.2 J L) z := by
  have hEq : phaseHessianPairing g J L =ᶠ[𝓝 z]
      fun y : Phase => hermitianPrincipalHessianPairing (g y.1) y.2 J L := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hz] with y hy
    exact phaseHessianPairing_eq_hermitianPrincipalHessianPairing g y (hG y.1 hy) J L hJ hL
  exact hEq.fderiv_eq

end Burnett.V02
