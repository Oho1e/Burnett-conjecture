import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleRawTrilinear
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 14500000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.V08 (signedCyclicPhase)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open Burnett.P01 (ComplexComponents)

open private wardGaugePotentialAt from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
open private wardRaisedEntryLinear wardRaisedEntryLinear_apply wardThreeProduct wardThreeProduct_apply wardEntryLinear wardEntryLinear_apply wardRaisedGaugeLinear wardRaisedGaugeLinear_apply from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleRawTrilinear

private def wardLowLieFirstTrilinear (m : Tensor2) (p : E) : WardTensorTrilinear :=
  (1 / 4 : ℂ) • (∑ a : Index, ∑ b : Index, ∑ c : Index,
    ((p a : ℂ) • wardThreeProduct (wardRaisedGaugeLinear m p c) (wardRaisedEntryLinear m a b) (wardEntryLinear c b) +
    (p b : ℂ) • wardThreeProduct (wardRaisedGaugeLinear m p c) (wardRaisedEntryLinear m a b) (wardEntryLinear c a)))

private def wardLowLieSecondTrilinear (m : Tensor2) (p : E) : WardTensorTrilinear :=
  (1 / 4 : ℂ) • (∑ a : Index, ∑ b : Index, ∑ c : Index,
    ((p a : ℂ) • wardThreeProduct (wardRaisedGaugeLinear m p c) (wardEntryLinear c b) (wardRaisedEntryLinear m a b) +
    (p b : ℂ) • wardThreeProduct (wardRaisedGaugeLinear m p c) (wardEntryLinear c a) (wardRaisedEntryLinear m a b)))

private theorem wardLowLieFirstTrilinear_apply (m : Tensor2) (p : E) (H : Fin 3 → ComplexComponents) :
    wardLowLieFirstTrilinear m p H = wardScreenLieContraction m (H 1) (H 2) (wardGaugePotentialAt p (H 0)) p := by
  rw [wardScreenLieContraction, wardFrozenScreenPair_eq_raised]
  simp only [wardLowLieFirstTrilinear, MultilinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.add_apply,
    smul_eq_mul, wardThreeProduct_apply, wardRaisedEntryLinear_apply, wardEntryLinear_apply, wardRaisedGaugeLinear_apply,
    wardLieGaugeInsertion, wardLieVector]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [add_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem wardLowLieSecondTrilinear_apply (m : Tensor2) (p : E) (H : Fin 3 → ComplexComponents) :
    wardLowLieSecondTrilinear m p H = wardScreenLieContraction m (H 2) (H 1) (wardGaugePotentialAt p (H 0)) p := by
  rw [wardScreenLieContraction, wardFrozenScreenPair_eq_raised]
  simp only [wardLowLieSecondTrilinear, MultilinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.add_apply,
    smul_eq_mul, wardThreeProduct_apply, wardRaisedEntryLinear_apply, wardEntryLinear_apply, wardRaisedGaugeLinear_apply,
    wardLieGaugeInsertion, wardLieVector]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [add_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The two genuine physical Lie-index phases of the original one-low-gauge
formula are trilinear in the gauge and the two thin Fourier inputs. -/
def wardOneLowGaugeLieRawTrilinear (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) : WardTensorTrilinear :=
  ((-2 : ℂ) * (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ)) •
    ((quadratic m x.2 : ℂ) • wardLowLieFirstTrilinear m x.1 +
      (quadratic m (-(x.1+x.2)) : ℂ) • wardLowLieSecondTrilinear m x.1)

theorem wardOneLowGaugeLieRawTrilinear_apply (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint)
    (H : Fin 3 → ComplexComponents) :
    wardOneLowGaugeLieRawTrilinear m w a x H = wardOneLowGaugeLieRaw m w a (H 0) (H 1) (H 2) x := by
  simp only [wardOneLowGaugeLieRawTrilinear, MultilinearMap.smul_apply, MultilinearMap.add_apply, smul_eq_mul,
    wardLowLieFirstTrilinear_apply, wardLowLieSecondTrilinear_apply, wardOneLowGaugeLieRaw]

end Burnett.C02
