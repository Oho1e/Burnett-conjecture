import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers

set_option autoImplicit false
set_option maxRecDepth 6800
set_option maxHeartbeats 12600000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open Burnett.P01 (ComplexComponents)
open scoped Matrix

open private raisedWardScreenEntry raisedWardGaugeComponent from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers

private def wardRaisedScreenContraction (m : Mat) (H : ComplexComponents) (p : E) (u : ComplexCovector) : ℂ :=
  ∑ a, ∑ b, raisedWardScreenEntry m H a b * (p a : ℂ) * u b

private theorem wardRaisedScreenEntry_symmetric (m : Mat) (H : ComplexComponents) (hH : IsSymmetricComplexTensor H)
    (a b : Index) : raisedWardScreenEntry m H a b = raisedWardScreenEntry m H b a := by
  unfold raisedWardScreenEntry
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hH i j]
  ring

/-- Both symmetric terms of the gauge insertion combine into one ordered
contraction against the twice-raised physical slot. -/
theorem wardFrozenScreenPair_pureGauge (m : Mat) (H : ComplexComponents) (hH : IsSymmetricComplexTensor H)
    (p : E) (u : ComplexCovector) :
    frozenWardScreenPair m H (complexPureGauge (fun a => p a) u) =
      (1 / 2 : ℂ) * wardRaisedScreenContraction m H p u := by
  have h (a b : Index) : complexPureGauge (fun a => p a) u a b * raisedWardScreenEntry m H a b =
      raisedWardScreenEntry m H a b * (p a : ℂ) * u b +
      raisedWardScreenEntry m H a b * (p b : ℂ) * u a := by
    unfold complexPureGauge
    ring
  have hSwap : (∑ a, ∑ b, raisedWardScreenEntry m H a b * (p b : ℂ) * u a) =
      wardRaisedScreenContraction m H p u := by
    unfold wardRaisedScreenContraction
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [wardRaisedScreenEntry_symmetric m H hH b a]
  rw [wardFrozenScreenPair_eq_raised]
  simp only [h, Finset.sum_add_distrib, hSwap]
  change (1 / 4 : ℂ) * (wardRaisedScreenContraction m H p u + wardRaisedScreenContraction m H p u) = _
  ring

private theorem wardRaisedScreenContraction_eq_zero (m : Mat) (H : ComplexComponents) (p : E)
    (u : ComplexCovector) (hp : ∀ b, ∑ a, raisedWardScreenEntry m H a b * (p a : ℂ) = 0) :
    wardRaisedScreenContraction m H p u = 0 := by
  unfold wardRaisedScreenContraction
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  rw [← Finset.sum_mul, hp b, zero_mul]

private theorem wardRaisedScreenContraction_signedThird (m : Mat) (H : ComplexComponents) (p q : E)
    (u : ComplexCovector) :
    wardRaisedScreenContraction m H (-(p+q)) u =
      -wardRaisedScreenContraction m H p u - wardRaisedScreenContraction m H q u := by
  have h (a b : Index) :
      raisedWardScreenEntry m H a b * ((-(p+q)) a : ℂ) * u b =
        -(raisedWardScreenEntry m H a b * (p a : ℂ) * u b) -
          raisedWardScreenEntry m H a b * (q a : ℂ) * u b := by
    simp only [PiLp.neg_apply, PiLp.add_apply, Complex.ofReal_add, Complex.ofReal_neg]
    ring
  simp only [wardRaisedScreenContraction, h, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

private theorem wardHighGaugeLieContraction (m : Mat) (H J : ComplexComponents)
    (hH : IsSymmetricComplexTensor H) (hJ : IsSymmetricComplexTensor J) (p q : E) (v : ComplexCovector)
    (hp : ∀ b, ∑ a, raisedWardScreenEntry m H a b * (p a : ℂ) = 0) :
    wardScreenLieContraction m H J v (-(p+q)) =
      -(1 / 2 : ℂ) * ∑ a, ∑ b, ∑ c, raisedWardScreenEntry m H a b *
        (q a : ℂ) * J b c * raisedWardGaugeComponent m v c := by
  have hInsert : wardLieGaugeInsertion m J v (-(p+q)) =
      complexPureGauge (fun a => (-(p+q)) a) (wardLieVector m J v) := by
    ext a b
    change ((-(p+q)) a : ℂ) * wardLieVector m J v b + ((-(p+q)) b : ℂ) * wardLieVector m J v a =
      ((-(p+q)) a : ℂ) * wardLieVector m J v b + wardLieVector m J v a * ((-(p+q)) b : ℂ)
    ring
  rw [wardScreenLieContraction, hInsert, wardFrozenScreenPair_pureGauge m H hH,
    wardRaisedScreenContraction_signedThird, wardRaisedScreenContraction_eq_zero m H p _ hp]
  have hCon : wardRaisedScreenContraction m H q (wardLieVector m J v) =
      ∑ a, ∑ b, ∑ c, raisedWardScreenEntry m H a b * (q a : ℂ) * J b c * raisedWardGaugeComponent m v c := by
    simp only [wardRaisedScreenContraction, wardLieVector, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [hJ c b]
    ring
  rw [hCon]
  ring

private theorem wardHighGaugeGeneratorDot (m : Mat) (v : ComplexCovector) (q : E) :
    raisedWardGaugeDot m v q = ∑ i, raisedWardGaugeComponent m v i * (q i : ℂ) := by
  simp only [raisedWardGaugeDot, raisedWardGaugeComponent, Finset.sum_mul]

/-- The true frozen Ward vertex with the gauge at the signed third
frequency has exactly the two designated physical phase brackets. -/
theorem wardLorentz_highGauge_screen_components (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (p q : E) (v : ComplexCovector)
    (H J : ComplexComponents) (hHs : IsSymmetricComplexTensor H) (hJs : IsSymmetricComplexTensor J)
    (hB : IsSymmetricTensor (inverseMatrix G))
    (htH : complexMetricTrace (inverseMatrix G) H = 0) (htJ : complexMetricTrace (inverseMatrix G) J = 0)
    (hpH : ∀ a, complexContracted (inverseMatrix G) (fun b => p b) H a = 0)
    (hqJ : ∀ a, complexContracted (inverseMatrix G) (fun b => q b) J a = 0)
    (hHP : ∀ b, ∑ a, raisedWardScreenEntry (inverseMatrix G) H a b * (p a : ℂ) = 0)
    (hJQ : ∀ b, ∑ a, raisedWardScreenEntry (inverseMatrix G) J a b * (q a : ℂ) = 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let w := (metricDensity G : ℂ)
    let C := frozenWardScreenPair B H J
    complexPrincipalVertex G (fun a => p a) H (fun a => q a) J (fun a => r a)
      (complexPureGauge (fun a => r a) v) =
      w * ((quadratic B p : ℂ) * wardHighGaugeBracket B C H J v q +
        (quadratic B q : ℂ) * wardHighGaugeBracket B C J H v p) := by
  intro r B w C
  have hcon (a : Index) : r a + p a + q a = 0 := by
    simp only [r, PiLp.neg_apply, PiLp.add_apply]
    ring
  have hr : -(q+p) = r := by rw [add_comm q p]
  have hOther := wardHighGaugeLieContraction B J H hJs hHs q p v hJQ
  rw [hr] at hOther
  rw [← complexPrincipalVertex_cyclic G (fun a => r a) (complexPureGauge (fun a => r a) v)
      (fun a => p a) H (fun a => q a) J,
    complexPrincipalVertex_one_pureGauge_ward_einsteinDensity G hG hGsym f (fun a => r a) (fun a => p a)
      (fun a => q a) v H J hHs hJs hcon,
    wardEinsteinDensityPairing_screen B (metricDensity G) p H _ htH hpH,
    wardEinsteinDensityPairing_screen B (metricDensity G) q J _ htJ hqJ,
    wardFrozenScreenPair_lie, wardFrozenScreenPair_lie, wardFrozenScreenPair_comm B hB J H,
    wardHighGaugeLieContraction B H J hHs hJs p q v hHP, hOther]
  simp only [wardHighGaugeBracket, wardHighGaugeGeneratorDot, B, C, w]
  ring

end Burnett.C02
