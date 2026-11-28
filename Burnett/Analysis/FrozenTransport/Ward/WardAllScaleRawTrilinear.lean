import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorAssembly
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualComparable
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 16400000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.RicciSymbol Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.P01 (ComplexComponents)
open Burnett.Analysis.ProjectiveNullCaps (quadratic lowSlotWeight comparableSlotWeight)
open Burnett.V08 (signedCyclicPhase normalizedGaugePotential)
open scoped Matrix

open private wardGaugePotentialAt wardTwoGaugePair raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
open private raisedWardScreenEntry raisedWardGaugeComponent from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
open private normalizedGaugePotentialLinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
open private wardComparableSymbol_eq wardExtendedTriadSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

private abbrev WardEntry := ComplexComponents →ₗ[ℂ] ℂ

private def wardEntryLinear (a b : Index) : WardEntry where
  toFun H := H a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def wardRaisedEntryLinear (m : Tensor2) (a b : Index) : WardEntry :=
  ∑ i : Index, ∑ j : Index, ((m a i : ℂ) * (m b j : ℂ)) • wardEntryLinear i j

private theorem wardRaisedEntryLinear_apply (m : Tensor2) (a b : Index) (H : ComplexComponents) :
    wardRaisedEntryLinear m a b H = raisedWardScreenEntry m H a b := by
  simp only [wardRaisedEntryLinear, LinearMap.sum_apply, LinearMap.smul_apply, wardEntryLinear,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, raisedWardScreenEntry]

private def wardPotentialEntryLinear (p : E) (i : Index) : WardEntry :=
  ((‖p‖⁻¹ : ℝ) : ℂ) • (LinearMap.proj i).comp (normalizedGaugePotentialLinear (endpointDirection p))

private theorem wardPotentialEntryLinear_apply (p : E) (i : Index) (H : ComplexComponents) :
    wardPotentialEntryLinear p i H = wardGaugePotentialAt p H i := rfl

private def wardRaisedGaugeLinear (m : Tensor2) (p : E) (i : Index) : WardEntry :=
  ∑ j : Index, (m i j : ℂ) • wardPotentialEntryLinear p j

private theorem wardRaisedGaugeLinear_apply (m : Tensor2) (p : E) (i : Index) (H : ComplexComponents) :
    wardRaisedGaugeLinear m p i H = raisedWardGaugeComponent m (wardGaugePotentialAt p H) i := by
  simp only [wardRaisedGaugeLinear, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    wardPotentialEntryLinear_apply, raisedWardGaugeComponent]

private def wardGaugeDotEntryLinear (m : Tensor2) (p q : E) : WardEntry :=
  ∑ i : Index, (q i : ℂ) • wardRaisedGaugeLinear m p i

private theorem wardGaugeDotEntryLinear_apply (m : Tensor2) (p q : E) (H : ComplexComponents) :
    wardGaugeDotEntryLinear m p q H = ∑ i, raisedWardGaugeComponent m (wardGaugePotentialAt p H) i * (q i : ℂ) := by
  simp only [wardGaugeDotEntryLinear, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    wardRaisedGaugeLinear_apply, mul_comm]

private def wardScreenQuadraticLinear (m : Tensor2) (p : E) : WardEntry :=
  ∑ a : Index, ∑ b : Index, ((p a : ℂ) * (p b : ℂ)) • wardRaisedEntryLinear m a b

private theorem wardScreenQuadraticLinear_apply (m : Tensor2) (p : E) (H : ComplexComponents) :
    wardScreenQuadraticLinear m p H = raisedScreenBilinear m H p p := by
  simp only [wardScreenQuadraticLinear, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    wardRaisedEntryLinear_apply, raisedScreenBilinear]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private def wardThreeProduct (A B C : WardEntry) : WardTensorTrilinear :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compLinearMap ![A,B,C]

private theorem wardThreeProduct_apply (A B C : WardEntry) (H : Fin 3 → ComplexComponents) :
    wardThreeProduct A B C H = A (H 0) * B (H 1) * C (H 2) := by
  simp only [wardThreeProduct, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

private theorem wardEntryLinear_apply (a b : Index) (H : ComplexComponents) : wardEntryLinear a b H = H a b := rfl

/-- Tensor form of the original two-gauge symbol with the physical slot first. -/
def wardTwoGaugePhysicalRawTrilinear (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) : WardTensorTrilinear :=
  let r := -(x.1 + x.2)
  ((signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.1 : ℂ)) •
    ∑ c : Index, wardThreeProduct (wardScreenQuadraticLinear m x.2)
      (wardRaisedGaugeLinear m x.2 c) (wardPotentialEntryLinear r c)

theorem wardTwoGaugePhysicalRawTrilinear_apply (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint)
    (H : Fin 3 → ComplexComponents) :
    wardTwoGaugePhysicalRawTrilinear m w a x H = wardTwoGaugePhysicalLowRaw m w a (H 1) (H 2) (H 0) x := by
  simp only [wardTwoGaugePhysicalRawTrilinear, MultilinearMap.smul_apply, MultilinearMap.sum_apply, smul_eq_mul,
    wardThreeProduct_apply, wardScreenQuadraticLinear_apply, wardPotentialEntryLinear_apply, wardRaisedGaugeLinear_apply,
    wardTwoGaugePhysicalLowRaw, wardTwoGaugeBracket, wardTwoGaugePair, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Tensor form of the original two-gauge symbol with the low gauge first. -/
def wardTwoGaugeGaugeRawTrilinear (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) : WardTensorTrilinear :=
  let r := -(x.1 + x.2)
  ((signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.2 : ℂ)) •
    ∑ c : Index, wardThreeProduct (wardRaisedGaugeLinear m x.1 c)
      (wardScreenQuadraticLinear m x.1) (wardPotentialEntryLinear r c)

theorem wardTwoGaugeGaugeRawTrilinear_apply (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint)
    (H : Fin 3 → ComplexComponents) :
    wardTwoGaugeGaugeRawTrilinear m w a x H = wardTwoGaugeGaugeLowRaw m w a (H 0) (H 2) (H 1) x := by
  simp only [wardTwoGaugeGaugeRawTrilinear, MultilinearMap.smul_apply, MultilinearMap.sum_apply, smul_eq_mul,
    wardThreeProduct_apply, wardScreenQuadraticLinear_apply, wardPotentialEntryLinear_apply, wardRaisedGaugeLinear_apply,
    wardTwoGaugeGaugeLowRaw, wardTwoGaugeBracket, wardTwoGaugePair, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

private def wardHighGaugeFirstTrilinear (m : Tensor2) (q r : E) : WardTensorTrilinear :=
  (-(1 / 2) : ℂ) • (∑ a : Index, ∑ b : Index, wardThreeProduct (wardRaisedEntryLinear m a b)
       (wardEntryLinear a b) (wardGaugeDotEntryLinear m r q)) +
    ∑ a : Index, ∑ b : Index, ∑ c : Index, (q a : ℂ) • wardThreeProduct (wardRaisedEntryLinear m a b)
      (wardEntryLinear b c) (wardRaisedGaugeLinear m r c)

private def wardHighGaugeSecondTrilinear (m : Tensor2) (p r : E) : WardTensorTrilinear :=
  (-(1 / 2) : ℂ) • (∑ a : Index, ∑ b : Index, wardThreeProduct (wardEntryLinear a b)
       (wardRaisedEntryLinear m a b) (wardGaugeDotEntryLinear m r p)) +
    ∑ a : Index, ∑ b : Index, ∑ c : Index, (p a : ℂ) • wardThreeProduct (wardEntryLinear b c)
      (wardRaisedEntryLinear m a b) (wardRaisedGaugeLinear m r c)

private theorem wardTransportPairFactor (F : Index → Index → ℂ) (d : ℂ) :
    -(1 / 2 : ℂ) * (∑ a, ∑ b, F a b * d) =
      (-2 * d) * ((1 / 4 : ℂ) * ∑ a, ∑ b, F a b) := by
  simp only [← Finset.sum_mul]
  ring

private theorem wardHighGaugeFirstTrilinear_apply (m : Tensor2) (q r : E) (H : Fin 3 → ComplexComponents) :
    wardHighGaugeFirstTrilinear m q r H =
      wardHighGaugeBracket m (frozenWardScreenPair m (H 0) (H 1)) (H 0) (H 1)
        (wardGaugePotentialAt r (H 2)) q := by
  simp only [wardHighGaugeFirstTrilinear, MultilinearMap.add_apply, MultilinearMap.smul_apply,
    MultilinearMap.sum_apply, smul_eq_mul, wardThreeProduct_apply, wardRaisedEntryLinear_apply,
    wardEntryLinear_apply, wardGaugeDotEntryLinear_apply, wardRaisedGaugeLinear_apply, wardHighGaugeBracket,
    wardFrozenScreenPair_eq_raised]
  congr 1
  · simpa only [mul_comm (raisedWardScreenEntry m (H 0) _ _) (H 1 _ _)] using
      wardTransportPairFactor (fun a b => H 1 a b * raisedWardScreenEntry m (H 0) a b)
        (∑ i, raisedWardGaugeComponent m (wardGaugePotentialAt r (H 2)) i * (q i : ℂ))
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring

private theorem wardHighGaugeSecondTrilinear_apply (m : Tensor2) (p r : E) (H : Fin 3 → ComplexComponents)
    (hm : IsSymmetricTensor m) :
    wardHighGaugeSecondTrilinear m p r H =
      wardHighGaugeBracket m (frozenWardScreenPair m (H 0) (H 1)) (H 1) (H 0)
        (wardGaugePotentialAt r (H 2)) p := by
  rw [wardFrozenScreenPair_comm m hm (H 0) (H 1)]
  simp only [wardHighGaugeSecondTrilinear, MultilinearMap.add_apply, MultilinearMap.smul_apply,
    MultilinearMap.sum_apply, smul_eq_mul, wardThreeProduct_apply, wardRaisedEntryLinear_apply,
    wardEntryLinear_apply, wardGaugeDotEntryLinear_apply, wardRaisedGaugeLinear_apply, wardHighGaugeBracket,
    wardFrozenScreenPair_eq_raised]
  congr 1
  · exact wardTransportPairFactor (fun a b => H 0 a b * raisedWardScreenEntry m (H 1) a b)
      (∑ i, raisedWardGaugeComponent m (wardGaugePotentialAt r (H 2)) i * (p i : ℂ))
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring

/-- Tensor form of the original one-high-gauge branch, before either
the first-low or comparable triad cutoff. -/
def wardOneHighGaugeRawTrilinear (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) : WardTensorTrilinear :=
  let r := -(x.1 + x.2)
  ((signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ)) •
    ((quadratic m x.1 : ℂ) • wardHighGaugeFirstTrilinear m x.2 r +
      (quadratic m x.2 : ℂ) • wardHighGaugeSecondTrilinear m x.1 r)

theorem wardOneHighGaugeRawTrilinear_apply (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint)
    (H : Fin 3 → ComplexComponents) (hm : IsSymmetricTensor m) :
    wardOneHighGaugeRawTrilinear m w a x H = wardOneHighGaugeRaw m w a (H 2) (H 0) (H 1) x := by
  simp only [wardOneHighGaugeRawTrilinear, MultilinearMap.smul_apply, MultilinearMap.add_apply,
    smul_eq_mul, wardHighGaugeFirstTrilinear_apply, wardHighGaugeSecondTrilinear_apply _ _ _ _ hm,
    wardOneHighGaugeRaw]
  rfl

def wardFirstLowTrilinear (ϑ : ℝ → ℝ) (κ : ℝ) (A : Joint → WardTensorTrilinear)
    (x : Joint) : WardTensorTrilinear := by
  classical
  exact if x.1 ≠ 0 ∧ x.2 ≠ 0 then
    (lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) • A x
  else 0

theorem wardFirstLowTrilinear_apply (ϑ : ℝ → ℝ) (κ : ℝ) (A : Joint → WardTensorTrilinear)
    (H : Fin 3 → ComplexComponents) (x : Joint) :
    wardFirstLowTrilinear ϑ κ A x H = wardActualLowCut ϑ κ (fun y => A y H) x := by
  classical
  by_cases h : x.1 ≠ 0 ∧ x.2 ≠ 0
  · simp only [wardFirstLowTrilinear, wardActualLowCut, if_pos h, MultilinearMap.smul_apply, smul_eq_mul]
  · simp only [wardFirstLowTrilinear, wardActualLowCut, if_neg h, MultilinearMap.zero_apply]

def wardComparableTrilinear (ϑ : ℝ → ℝ) (κ : ℝ) (A : Joint → WardTensorTrilinear)
    (x : Joint) : WardTensorTrilinear := by
  classical
  exact if x ∈ wardTriadDomain then
    (comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) : ℂ) • A x
  else 0

theorem wardComparableTrilinear_apply (ϑ : ℝ → ℝ) (κ : ℝ) (A : Joint → WardTensorTrilinear)
    (H : Fin 3 → ComplexComponents) (x : Joint) :
    wardComparableTrilinear ϑ κ A x H = wardComparableSymbol ϑ κ (fun y => A y H) x := by
  classical
  rw [wardComparableSymbol_eq]
  by_cases h : x ∈ wardTriadDomain
  · simp only [wardComparableTrilinear, if_pos h, MultilinearMap.smul_apply, smul_eq_mul,
      wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ h]
  · simp only [wardComparableTrilinear, if_neg h, MultilinearMap.zero_apply, wardExtendedTriadSymbol,
      piecewise_eq_of_notMem _ _ _ h]
    change 0 = _ * 0
    rw [mul_zero]

end Burnett.C02
