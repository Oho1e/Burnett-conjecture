import Burnett.Analysis.FrozenTransport.Ward.WardAffineKinetic
import Burnett.Analysis.TransportWard.HessianPhase

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 11400000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Set Filter Matrix Burnett.RicciSymbol Burnett.Geometry.TensorCoordinateChange
open scoped Matrix Topology

def wardAffineCovector (A : Mat) (p : Cov) : Cov := p ᵥ* A

theorem wardAffineMetric_symm (A H : Mat) (hH : IsSymmetricTensor H) : IsSymmetricTensor (pullbackMetric H A) := by
  have h : Hᵀ = H := by ext b c; exact hH c b
  have he : (pullbackMetric H A)ᵀ = pullbackMetric H A := by
    simp only [pullbackMetric, transpose_mul, transpose_transpose, h, mul_assoc]
  intro b c
  exact (congrArg (fun Q : Mat => Q b c) he).symm

theorem wardAffinePlaneJet (A : Mat) (p : Cov) (H : Mat) :
    wardAffineJet A (planeJet p H) = planeJet (wardAffineCovector A p) (pullbackMetric H A) := by
  funext b
  let q := wardAffineCovector A p
  have he : (∑ i : Fin 4, A i b • planeJet p H i) = q b • H := by
    have h (i : Fin 4) : planeJet p H i = p i • H := rfl
    simp only [h, smul_smul, ← Finset.sum_smul, q, wardAffineCovector, vecMul, dotProduct, mul_comm]
  change Aᵀ * (∑ i : Fin 4, A i b • planeJet p H i) * A = q b • (Aᵀ * H * A)
  rw [he, mul_smul_comm, smul_mul_assoc]

private theorem wardAffineMetric_path (A G H : Mat) (t : ℝ) :
    pullbackMetric (G + t • H) A = pullbackMetric G A + t • pullbackMetric H A := by
  simp only [pullbackMetric, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/-- Differentiate the genuine affine covariance of the quadratic action
coefficient in the undifferentiated metric direction. -/
theorem principalLeg_affine (A G H : Mat) (hA : IsUnit A) (hG : G.det ≠ 0)
    (hGsym : IsSymmetricTensor G) (hHsym : IsSymmetricTensor H)
    (X Y : Jet) (hXsym : ∀ d, IsSymmetricTensor (X d)) (hYsym : ∀ d, IsSymmetricTensor (Y d)) :
    principalLeg (pullbackMetric G A) (pullbackMetric H A) (wardAffineJet A X) (wardAffineJet A Y) =
      |A.det| * principalLeg G H X Y := by
  have hAd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hG' : (pullbackMetric G A).det ≠ 0 := by
    simp only [pullbackMetric, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hAd hG) hAd
  have hD : ∀ᶠ t : ℝ in 𝓝 0, (G + t • H).det ≠ 0 := by
    have hCont := (hasDerivAt_det_path G H).continuousAt
    exact hCont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simpa only [zero_smul, add_zero] using hG))
  have hEq : (fun t : ℝ => metricKineticCoefficient (pullbackMetric G A + t • pullbackMetric H A)
        (wardAffineJet A X) (wardAffineJet A Y)) =ᶠ[𝓝 0]
      (fun t : ℝ => |A.det| * metricKineticCoefficient (G + t • H) X Y) := by
    filter_upwards [hD] with t ht
    have hS : IsSymmetricTensor (G + t • H) := by
      intro b c
      simp only [Matrix.add_apply, Matrix.smul_apply, hGsym b c, hHsym b c]
    have hU : IsUnit (G + t • H) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
    rw [← wardAffineMetric_path]
    exact metricKineticCoefficient_affine A (G + t • H) hA hU hS X Y hXsym hYsym
  have hL := hasDerivAt_metricKineticCoefficient_path (pullbackMetric G A) (pullbackMetric H A) hG'
    (wardAffineJet A X) (wardAffineJet A Y)
  have hR := (hasDerivAt_metricKineticCoefficient_path G H hG X Y).const_mul |A.det|
  exact hL.unique (hR.congr_of_eventuallyEq hEq)

private theorem wardPlaneJet_symm (p : Cov) (H : Mat) (hH : IsSymmetricTensor H) (d : Fin 4) :
    IsSymmetricTensor (planeJet p H d) := by
  intro a b
  simp only [planeJet, hH a b]

theorem principalVertex_affine (A G : Mat) (hA : IsUnit A) (hG : G.det ≠ 0) (hGsym : IsSymmetricTensor G)
    (p q r : Cov) (H J L : Mat) (hH : IsSymmetricTensor H) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalVertex (pullbackMetric G A) (wardAffineCovector A p) (pullbackMetric H A)
        (wardAffineCovector A q) (pullbackMetric J A) (wardAffineCovector A r) (pullbackMetric L A) =
      |A.det| * principalVertex G p H q J r L := by
  simp only [principalVertex, ← wardAffinePlaneJet]
  rw [principalLeg_affine A G H hA hG hGsym hH _ _ (wardPlaneJet_symm q J hJ) (wardPlaneJet_symm r L hL),
    principalLeg_affine A G J hA hG hGsym hJ _ _ (wardPlaneJet_symm p H hH) (wardPlaneJet_symm r L hL),
    principalLeg_affine A G L hA hG hGsym hL _ _ (wardPlaneJet_symm p H hH) (wardPlaneJet_symm q J hJ)]
  ring

theorem principalHessianPairing_affine (A G : Mat) (hA : IsUnit A) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (p : Cov) (J L : Mat) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalHessianPairing (pullbackMetric G A) (wardAffineCovector A p) (pullbackMetric J A) (pullbackMetric L A) =
      |A.det| * principalHessianPairing G p J L := by
  have hn : -wardAffineCovector A p = wardAffineCovector A (-p) := by simp [wardAffineCovector, neg_vecMul]
  simp only [principalHessianPairing, hn, ← wardAffinePlaneJet]
  rw [metricKineticCoefficient_affine A G hA hG hGsym _ _ (wardPlaneJet_symm p J hJ) (wardPlaneJet_symm (-p) L hL)]
  ring

end Burnett.Analysis.TransportWardSymbol
