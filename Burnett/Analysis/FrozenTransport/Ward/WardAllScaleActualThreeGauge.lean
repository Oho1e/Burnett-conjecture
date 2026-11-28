import Burnett.Analysis.FrozenTransport.Ward.WardAffineLorentz
import Burnett.Analysis.TransportWard.ComplexWard
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection

set_option autoImplicit false
set_option maxRecDepth 6800
set_option maxHeartbeats 10400000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.Geometry.TensorCoordinateChange
open scoped Matrix

/-- The actual real Lorentzian frozen vertex has exact cancellation on
three pure gauges for every signed triad. -/
theorem principalVertex_three_pureGauge_lorentz (G : Mat) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (p q r v w z : Cov) (hcon : ∀ a, p a + q a + r a = 0) :
    principalVertex G p (pureGauge p v) q (pureGauge q w) r (pureGauge r z) = 0 := by
  let A : Mat := Matrix.of f.components
  obtain ⟨hA,hη⟩ := wardFrame_affineEta G hG f
  have hS : p + q + r = 0 := funext hcon
  have hS' : wardAffineCovector A p + wardAffineCovector A q + wardAffineCovector A r = 0 := by
    have h := congrArg (wardAffineCovector A) hS
    simpa only [wardAffineCovector, add_vecMul, zero_vecMul] using h
  have hconA (a : Fin 4) : wardAffineCovector A p a + wardAffineCovector A q a + wardAffineCovector A r a = 0 :=
    congrFun hS' a
  have hA' : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hG' : G.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hSym (p v : Cov) : IsSymmetricTensor (pureGauge p v) := by
    intro a b
    simp only [pureGauge]
    ring
  have hh := principalVertex_eta_three_pureGauge (wardAffineCovector A p) (wardAffineCovector A q)
    (wardAffineCovector A r) (wardAffineCovector A v) (wardAffineCovector A w) (wardAffineCovector A z) hconA
  rw [← wardAffinePureGauge, ← wardAffinePureGauge, ← wardAffinePureGauge, ← hη,
    principalVertex_affine A G hA hG' hGsym _ _ _ _ _ _ (hSym p v) (hSym q w) (hSym r z)] at hh
  exact (mul_eq_zero.mp hh).resolve_left (abs_ne_zero.mpr hA')

theorem complexPrincipalVertex_three_pureGauge_lorentz (G : Mat) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (p q r : Cov) (v w z : ComplexCovector) (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex G p (complexPureGauge p v) q (complexPureGauge q w) r (complexPureGauge r z) = 0 := by
  simp only [complexPrincipalVertex, realAmplitude_complexPureGauge, imagAmplitude_complexPureGauge,
    principalVertex_three_pureGauge_lorentz G hG hGsym f p q r _ _ _ hcon, sub_zero, add_zero,
    Complex.ofReal_zero, mul_zero]

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A02.FrequencySplit
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum originalLowGaugePotential normalizedGaugeAmplitude)
open scoped Matrix

private theorem wardActualGaugeSpectrum_eq_pureGauge (z : ProjectionSchwartzMatrix)
    (hSym : ∀ i j, z i j = z j i) (ξ : E) (hξ : ξ ≠ 0) :
    (originalGaugeSpectrum z ξ : ComplexTensor2) =
      complexPureGauge (fun i => ξ i) (originalLowGaugePotential z ξ) := by
  rw [Burnett.V08.originalGaugeSpectrum_eq_amplitude z hSym ξ hξ]
  rfl

/-- Exact cancellation with all three gauge legs taken from the same
original localized perturbation, on its actual signed Fourier triad. -/
theorem wardActualThreeGaugeVertex_eq_zero (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (z : ProjectionSchwartzMatrix)
    (hSym : ∀ i j, z i j = z j i) (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) (hr : -(p+q) ≠ 0) :
    complexPrincipalVertex G (fun i => p i) (originalGaugeSpectrum z p)
      (fun i => q i) (originalGaugeSpectrum z q) (fun i => (-(p+q)) i) (originalGaugeSpectrum z (-(p+q))) = 0 := by
  rw [wardActualGaugeSpectrum_eq_pureGauge z hSym p hp, wardActualGaugeSpectrum_eq_pureGauge z hSym q hq,
    wardActualGaugeSpectrum_eq_pureGauge z hSym (-(p+q)) hr]
  apply complexPrincipalVertex_three_pureGauge_lorentz G hG hGsym f
  intro a
  simp only [PiLp.neg_apply, PiLp.add_apply, add_neg_cancel]

end Burnett.C02
