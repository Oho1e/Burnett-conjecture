import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzHighGauge
import Burnett.Algebra.HermitianScreen
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 13300000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open Burnett.P01 (ComplexComponents)
open scoped Matrix

open private raisedWardScreenEntry raisedWardGaugeComponent from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private raisedScreenBilinear wardTwoGaugePair from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
open private wardScreenPairRight from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
open private wardComplexLieTensor_eq_slots from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
open private wardRaisedScreenContraction wardRaisedScreenContraction_eq_zero wardRaisedScreenContraction_signedThird from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzHighGauge

private theorem wardEinsteinDensityPairing_pureGauge_zero (m : Mat) (hm : IsSymmetricTensor m)
    (w : ℝ) (q : E) (u : ComplexCovector) (L : ComplexComponents) :
    wardEinsteinDensityPairing m w (fun a => q a) (complexPureGauge (fun a => q a) u) L = 0 := by
  have h : complexRicciSymbol m (fun a => q a) (complexPureGauge (fun a => q a) u) = 0 := by
    funext a b
    exact complexRicciSymbol_pureGauge_eq_zero m (fun a => q a) u hm a b
  simp only [wardEinsteinDensityPairing, einsteinDensitySymbol, h, raiseBoth, complexRaiseSecond, complexMetricTrace,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div, sub_zero]

private theorem wardLiePureGauge_cancellation (m : Mat) (p q : E) (u v : ComplexCovector) :
    let r := -(p+q)
    let A := raisedWardGaugeDot m v q
    let B := wardTwoGaugePair m u v
    (wardComplexLieTensor m (fun a => r a) v (fun a => q a)
        (complexPureGauge (fun a => q a) u) : ComplexComponents) =
      (-A) • (complexPureGauge (fun a => p a) u : ComplexComponents) +
        B • (complexPureGauge (fun a => r a) (fun a => (q a : ℂ)) : ComplexComponents) := by
  intro r A B
  have hv (j : Index) : wardLieVector m (complexPureGauge (fun a => q a) u) v j =
      A * u j + B * (q j : ℂ) := by
    simp only [wardLieVector, complexPureGauge, add_mul, Finset.sum_add_distrib]
    congr 1
    · change (∑ i, (q i : ℂ) * u j * raisedWardGaugeComponent m v i) = A * u j
      have hA : A = ∑ i, raisedWardGaugeComponent m v i * (q i : ℂ) := by
        simp only [A, raisedWardGaugeDot, raisedWardGaugeComponent, Finset.sum_mul]
      rw [hA, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · rw [show B = ∑ i, u i * raisedWardGaugeComponent m v i from rfl, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [wardComplexLieTensor_eq_slots]
  ext a b
  simp only [wardLieGaugeInsertion, complexPureGauge, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hv]
  change A * ((q a : ℂ) * u b + u a * (q b : ℂ)) +
    ((r a : ℂ) * (A * u b + B * (q b : ℂ)) + (r b : ℂ) * (A * u a + B * (q a : ℂ))) =
      (-A) * ((p a : ℂ) * u b + u a * (p b : ℂ)) + B * ((r a : ℂ) * (q b : ℂ) + (q a : ℂ) * (r b : ℂ))
  simp only [r, PiLp.neg_apply, PiLp.add_apply, Complex.ofReal_neg, Complex.ofReal_add]
  ring

private theorem wardScreenPair_liePureGauge (m : Mat) (H : ComplexComponents)
    (hH : IsSymmetricComplexTensor H) (p q : E) (u v : ComplexCovector)
    (hHP : ∀ b, ∑ a, raisedWardScreenEntry m H a b * (p a : ℂ) = 0) :
    frozenWardScreenPair m H (wardComplexLieTensor m (fun a => (-(p+q)) a) v (fun a => q a)
        (complexPureGauge (fun a => q a) u)) =
      -(1 / 2 : ℂ) * wardTwoGaugeBracket m H u v q := by
  change (wardScreenPairRight m H) (wardComplexLieTensor m (fun a => (-(p+q)) a) v (fun a => q a)
        (complexPureGauge (fun a => q a) u)) = _
  rw [wardLiePureGauge_cancellation, map_add, map_smul, map_smul]
  change _ * frozenWardScreenPair m H _ + _ * frozenWardScreenPair m H _ = _
  rw [wardFrozenScreenPair_pureGauge m H hH, wardFrozenScreenPair_pureGauge m H hH,
    wardRaisedScreenContraction_eq_zero m H p _ hHP, wardRaisedScreenContraction_signedThird,
    wardRaisedScreenContraction_eq_zero m H p _ hHP]
  unfold wardTwoGaugeBracket
  change _ = -(1 / 2 : ℂ) * (wardTwoGaugePair m u v * wardRaisedScreenContraction m H q (fun a => (q a : ℂ)))
  ring

theorem wardTwoGaugeBracket_swap (m : Mat) (hm : IsSymmetricTensor m) (H : ComplexComponents)
    (u v : ComplexCovector) (q : E) :
    wardTwoGaugeBracket m H u v q = wardTwoGaugeBracket m H v u q := by
  unfold wardTwoGaugeBracket
  congr 1
  simp only [wardTwoGaugePair, raisedWardGaugeComponent, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hm j k]
  ring

/-- The exact two-gauge formula from the action Ward identity. The only
remaining Hessian is on the physical slot at its original frequency. -/
theorem wardLorentz_twoGauge_screen_components (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (p q : E) (u v : ComplexCovector)
    (H : ComplexComponents) (hHs : IsSymmetricComplexTensor H)
    (hB : IsSymmetricTensor (inverseMatrix G))
    (htH : complexMetricTrace (inverseMatrix G) H = 0)
    (hpH : ∀ a, complexContracted (inverseMatrix G) (fun b => p b) H a = 0)
    (hHP : ∀ b, ∑ a, raisedWardScreenEntry (inverseMatrix G) H a b * (p a : ℂ) = 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let w := (metricDensity G : ℂ)
    complexPrincipalVertex G (fun a => p a) H (fun a => q a) (complexPureGauge (fun a => q a) u)
      (fun a => r a) (complexPureGauge (fun a => r a) v) =
      w * (quadratic B p : ℂ) * wardTwoGaugeBracket B H v u q := by
  intro r B w
  let Q := complexPureGauge (fun a => q a) u
  have hQs : IsSymmetricComplexTensor Q := by
    intro a b
    simp only [Q, complexPureGauge]
    ring
  have hcon (a : Index) : r a + p a + q a = 0 := by
    simp only [r, PiLp.neg_apply, PiLp.add_apply]
    ring
  rw [← complexPrincipalVertex_cyclic G (fun a => r a) (complexPureGauge (fun a => r a) v)
      (fun a => p a) H (fun a => q a) Q,
    complexPrincipalVertex_one_pureGauge_ward_einsteinDensity G hG hGsym f (fun a => r a)
      (fun a => p a) (fun a => q a) v H Q hHs hQs hcon,
    wardEinsteinDensityPairing_screen B (metricDensity G) p H _ htH hpH,
    wardEinsteinDensityPairing_pureGauge_zero B hB,
    wardScreenPair_liePureGauge B H hHs p q u v hHP,
    wardTwoGaugeBracket_swap B hB H u v, sub_zero]
  ring

end Burnett.C02
