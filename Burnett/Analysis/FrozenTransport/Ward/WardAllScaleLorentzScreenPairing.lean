import Burnett.Analysis.FrozenTransport.Ward.WardLorentzComplexDensity
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThinPhysical
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
import Burnett.Analysis.FrozenTransport.Ward.WardLorentzComplexKernel
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 14200000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open Burnett.P01 (ComplexComponents)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped Matrix

open private wardComplexRaisedGenerator from Burnett.Analysis.FrozenTransport.Ward.WardLorentzComplexKernel
open private raisedWardScreenEntry raisedWardGaugeComponent from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
open private wardScreenPairRight from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor

theorem wardRaiseBoth_eq_orderedEntry (m : Mat) (H : ComplexComponents) (a b : Index) :
    raiseBoth m H a b = raisedWardScreenEntry m H a b := by
  simp only [raiseBoth, complexRaiseSecond, raisedWardScreenEntry, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wardFrozenScreenPair_eq_raised (m : Mat) (H J : ComplexComponents) :
    frozenWardScreenPair m H J = (1 / 4 : ℂ) * ∑ a, ∑ b, J a b * raisedWardScreenEntry m H a b := by
  unfold frozenWardScreenPair raisedWardScreenEntry
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wardFrozenScreenPair_comm (m : Mat) (hm : IsSymmetricTensor m) (H J : ComplexComponents) :
    frozenWardScreenPair m H J = frozenWardScreenPair m J H := by
  let F (a b : OrderedPair) := (m a.1 b.1 : ℂ) * (m a.2 b.2 : ℂ) * H b.1 b.2 * J a.1 a.2
  have hH : frozenWardScreenPair m H J = (1 / 4 : ℂ) * ∑ a : OrderedPair, ∑ b : OrderedPair, F a b := by
    simp only [frozenWardScreenPair, Fintype.sum_prod_type, F]
  have hJ : frozenWardScreenPair m J H = (1 / 4 : ℂ) * ∑ b : OrderedPair, ∑ a : OrderedPair, F a b := by
    simp only [frozenWardScreenPair, Fintype.sum_prod_type, F]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hm a i, hm b j]
    ring
  rw [hH, hJ, Finset.sum_comm]

/-- The original physical phase, density and all 16 ordered receiving
components are retained in the Ward Hessian insertion. -/
theorem wardEinsteinDensityPairing_screen (m : Mat) (w : ℝ) (q : E) (H J : ComplexComponents)
    (ht : complexMetricTrace m H = 0) (hq : ∀ a, complexContracted m (fun b => q b) H a = 0) :
    wardEinsteinDensityPairing m w (fun b => q b) H J =
      2 * (w : ℂ) * (quadratic m q : ℂ) * frozenWardScreenPair m H J := by
  have h (a b : Index) : einsteinDensitySymbol m w (fun d => q d) H a b =
      (w : ℂ) * (quadratic m q : ℂ) / 2 * raisedWardScreenEntry m H a b := by
    rw [(einsteinDensitySymbol_screen_phase m w (fun d => q d) H ht hq a b).1,
      quadratic_eq_symbolNorm, wardRaiseBoth_eq_orderedEntry]
  rw [wardFrozenScreenPair_eq_raised]
  unfold wardEinsteinDensityPairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [h a b]
  ring

private theorem wardComplexLieTensor_eq_slots (m : Mat) (p r : E) (v : ComplexCovector) (J : ComplexComponents) :
    (wardComplexLieTensor m (fun a => p a) v (fun a => r a) J : ComplexComponents) =
      raisedWardGaugeDot m v r • J + wardLieGaugeInsertion m J v p := by
  have h : (∑ i, wardComplexRaisedGenerator m v i * (r i : ℂ)) = raisedWardGaugeDot m v r := by
    simp only [wardComplexRaisedGenerator, raisedWardGaugeDot, Finset.sum_mul]
  ext a b
  have hV (d : Index) : (∑ i, wardComplexRaisedGenerator m v i * J i d) = wardLieVector m J v d := by
    simp only [wardComplexRaisedGenerator, wardLieVector, raisedWardGaugeComponent, mul_comm]
  simp only [wardComplexLieTensor, h, complexPureGauge, hV, wardLieGaugeInsertion, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  change _ + ((p a : ℂ) * wardLieVector m J v b + wardLieVector m J v a * (p b : ℂ)) =
    _ + ((p a : ℂ) * wardLieVector m J v b + (p b : ℂ) * wardLieVector m J v a)
  rw [mul_comm (wardLieVector m J v a) (p b : ℂ)]

theorem wardFrozenScreenPair_lie (m : Mat) (p r : E) (v : ComplexCovector) (H J : ComplexComponents) :
    frozenWardScreenPair m H (wardComplexLieTensor m (fun a => p a) v (fun a => r a) J) =
      raisedWardGaugeDot m v r * frozenWardScreenPair m H J + wardScreenLieContraction m H J v p := by
  change (wardScreenPairRight m H) (wardComplexLieTensor m (fun a => p a) v (fun a => r a) J) = _
  rw [wardComplexLieTensor_eq_slots, map_add, map_smul]
  rfl

theorem raisedWardGaugeDot_signedThird (m : Mat) (v : ComplexCovector) (p q : E) :
    raisedWardGaugeDot m v (-(p+q)) = -raisedWardGaugeDot m v p - raisedWardGaugeDot m v q := by
  simp only [raisedWardGaugeDot, PiLp.neg_apply, PiLp.add_apply, Complex.ofReal_neg, Complex.ofReal_add,
    mul_neg, mul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

/-- Exact symmetric four-term expansion of the actual one-gauge Ward
vertex, including the full correction on the physical phase difference. -/
theorem wardLorentz_oneGauge_screen_components (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (p q : E) (v : ComplexCovector)
    (H J : ComplexComponents) (hHs : IsSymmetricComplexTensor H) (hJs : IsSymmetricComplexTensor J)
    (hB : IsSymmetricTensor (inverseMatrix G))
    (htH : complexMetricTrace (inverseMatrix G) H = 0) (htJ : complexMetricTrace (inverseMatrix G) J = 0)
    (hqH : ∀ a, complexContracted (inverseMatrix G) (fun b => q b) H a = 0)
    (hqJ : ∀ a, complexContracted (inverseMatrix G) (fun b => (-(p+q)) b) J a = 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let w := (metricDensity G : ℂ)
    let s := (quadratic B q : ℂ)
    let t := (quadratic B r : ℂ)
    let C := frozenWardScreenPair B H J
    complexPrincipalVertex G (fun a => p a) (complexPureGauge (fun a => p a) v)
      (fun a => q a) H (fun a => r a) J =
      -w * (t - s) * raisedWardGaugeDot B v (q-r) * C +
        w * raisedWardGaugeDot B v p * (s + t) * C -
        2 * w * s * wardScreenLieContraction B H J v p -
        2 * w * t * wardScreenLieContraction B J H v p := by
  intro r B w s t C
  have hcon (a : Index) : p a + q a + r a = 0 := by simp only [r, PiLp.neg_apply, PiLp.add_apply, add_neg_cancel]
  rw [complexPrincipalVertex_one_pureGauge_ward_einsteinDensity G hG hGsym f (fun a => p a) (fun a => q a)
      (fun a => r a) v H J hHs hJs hcon,
    wardEinsteinDensityPairing_screen B (metricDensity G) q H _ htH hqH,
    wardEinsteinDensityPairing_screen B (metricDensity G) r J _ htJ hqJ,
    wardFrozenScreenPair_lie, wardFrozenScreenPair_lie,
    wardFrozenScreenPair_comm B hB J H]
  have hSub : raisedWardGaugeDot B v (q-r) = raisedWardGaugeDot B v q - raisedWardGaugeDot B v r := by
    simp only [raisedWardGaugeDot, PiLp.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]
  rw [hSub]
  rw [show raisedWardGaugeDot B v r = _ from raisedWardGaugeDot_signedThird B v p q]
  ring

end Burnett.C02
