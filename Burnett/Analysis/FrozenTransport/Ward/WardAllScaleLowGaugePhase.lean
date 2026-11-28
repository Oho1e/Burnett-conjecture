import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 12400000
noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight lowSlotWeight_nonzero_small quadratic)
open Burnett.V08 (signedCyclicPhase normalizedGaugePotential)
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open scoped ContDiff

/-- The coefficient of the middle term of the exact low-gauge identity,
with its actual low weight and the two frozen phase factors. -/
def wardLowGaugeMiddleSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (G H J : ComplexComponents) (x : Joint) : ℂ := by
  classical
  exact if x.1 ≠ 0 ∧ x.2 ≠ 0 then
    let p := x.1
    let q := x.2
    let r := -(p+q)
    let v : Burnett.P01.ComplexCovector := fun j => (‖p‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection p) G j
    (lowSlotWeight ϑ κ p q r : ℂ) *
      ((signedCyclicPhase a p q : ℂ) * (w : ℂ) * raisedWardGaugeDot m v p *
        ((quadratic m q : ℂ) + (quadratic m r : ℂ)) * frozenWardScreenPair m H J)
    else 0

private theorem wardLowGaugeMiddleSymbol_eq_phase (ϑ : ℝ → ℝ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (G H J : ComplexComponents) (x : Joint) :
    wardLowGaugeMiddleSymbol ϑ κ m w a G H J x =
      wardLowRadialSymbol ϑ κ (fun y => (lowGaugeScalarPhaseProfiles m w a G H J y).1) x *
        (normalizedFrozenPhase m x.2 : ℂ) +
      wardLowRadialSymbol ϑ κ (fun y => (lowGaugeScalarPhaseProfiles m w a G H J y).2) x *
        (normalizedFrozenPhase m (-(x.1+x.2)) : ℂ) := by
  classical
  by_cases hx : x ∈ wardLowActive
  · let r := -(x.1+x.2)
    have hRatio : ‖x.1‖ / ‖x.2‖ < 1 / 2 := hx.2.2.trans (by norm_num)
    have hr : r ≠ 0 := by
      intro h
      have hEq : x.1 = -x.2 := eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h)
      rw [hEq, norm_neg, div_self (norm_ne_zero_iff.mpr hx.2.1)] at hRatio
      norm_num at hRatio
    have hpqr : ((‖x.1‖ * ‖x.2‖ * ‖r‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr hx.1) (norm_ne_zero_iff.mpr hx.2.1)) (norm_ne_zero_iff.mpr hr))
    have hId := (div_eq_iff hpqr).mp
      (lowGaugeScalarPhase_eq_normalized m w a ha hOdd hHom x.1 x.2 hx.1 hx.2.1 hRatio G H J)
    simp only [wardLowGaugeMiddleSymbol, if_pos (And.intro hx.1 hx.2.1), wardLowRadialSymbol,
      wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx, wardLowInput, endpointDirection]
    rw [hId]
    ring
  · have hOff (F : WardLowPoint → ℂ) : wardLowRadialSymbol ϑ κ F x = 0 := by
      simp only [wardLowRadialSymbol, wardLowSlotSymbol, piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, zero_mul]
    rw [hOff, hOff, zero_mul, zero_mul, add_zero, wardLowGaugeMiddleSymbol]
    split_ifs with h
    · have hL : lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) = 0 := by
        by_contra hL
        have hSupport := lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (x.1+x.2)) h.2 hL
        have hLe := (div_le_iff₀ (norm_pos_iff.mpr h.2)).mpr hSupport
        exact hx ⟨h.1, h.2, hLe.trans_lt (by linarith only [hSmall])⟩
      simp only [hL, Complex.ofReal_zero, zero_mul]
    · rfl

def wardTensorBasis (k : OrderedPair) : ComplexComponents := Matrix.single k.1 k.2 1

private theorem wardLowGaugeMiddleWeight_eq_phase (ϑ : ℝ → ℝ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (k l j : OrderedPair) (x : Joint) :
    let V := actualThinSchwartzField m wi wo hm hη i o z
    let P := actualWardPhaseSchwartz m wi wo hm hη i o z
    let G := projectedGaugeComplement z k.1 k.2
    let F := lowGaugeScalarPhaseProfiles m w a (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j)
    radianTrilinearWeight (wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis k)
        (wardTensorBasis l) (wardTensorBasis j)) G (V l) (V j) x =
      radianTrilinearWeight (wardLowRadialSymbol ϑ κ (fun y => (F y).1)) G (P l) (V j) x +
      radianTrilinearWeight (wardLowRadialSymbol ϑ κ (fun y => (F y).2)) G (V l) (P j) x := by
  intro V P G F
  have hPl (ξ : E) : radianFourier (P l) ξ = (normalizedFrozenPhase m ξ : ℂ) * radianFourier (V l) ξ :=
    actualWardPhaseSchwartz_radianFourier m wi wo hm hη i o z l ξ
  have hPj (ξ : E) : radianFourier (P j) ξ = (normalizedFrozenPhase m ξ : ℂ) * radianFourier (V j) ξ :=
    actualWardPhaseSchwartz_radianFourier m wi wo hm hη i o z j ξ
  simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul,
    wardLowGaugeMiddleSymbol_eq_phase ϑ hCut κ hκ hSmall m w a ha hOdd hHom, hPl, hPj, F]
  ring

/-- The actual Fourier integral for one ordered component of the middle
low-gauge Ward term. Each phase has been put on its own original physical
Schwartz slot, with the same gauge field, thin screen and infrared window. -/
theorem exists_actualWardLowGaugeMiddleComponent_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (k l j : OrderedPair) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ProjectionSchwartzMatrix),
      let V := actualThinSchwartzField m wi wo hm hη i o z
      let P := actualWardPhaseSchwartz m wi wo hm hη i o z
      let G := projectedGaugeComplement z k.1 k.2
      let M := wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j)
      Integrable (radianTrilinearWeight M G (V l) (V j)) ∧
      ‖radianTrilinearForm M G (V l) (V j)‖ ≤ C * wardCoordinateGradientL3 G *
        (wardCoordinateGradientL3 (P l) * wardCoordinateGradientL3 (V j) +
          wardCoordinateGradientL3 (V l) * wardCoordinateGradientL3 (P j)) := by
  let F := lowGaugeScalarPhaseProfiles m w a (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j)
  have hF := lowGaugeScalarPhaseProfiles_contDiffOn m w a ha (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j)
  obtain ⟨C₁,hC₁,h₁⟩ := exists_wardLowRadialForm_bound ϑ hϑ hCut κ hκ hSmall (fun x => (F x).1) hF.fst
  obtain ⟨C₂,hC₂,h₂⟩ := exists_wardLowRadialForm_bound ϑ hϑ hCut κ hκ hSmall (fun x => (F x).2) hF.snd
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), ?_⟩
  intro wi wo hm η hη i o z V P G M
  obtain ⟨hInt₁,hB₁⟩ := h₁ G (P l) (V j)
  obtain ⟨hInt₂,hB₂⟩ := h₂ G (V l) (P j)
  have hWeight : radianTrilinearWeight M G (V l) (V j) =
      radianTrilinearWeight (wardLowRadialSymbol ϑ κ (fun y => (F y).1)) G (P l) (V j) +
      radianTrilinearWeight (wardLowRadialSymbol ϑ κ (fun y => (F y).2)) G (V l) (P j) :=
    funext (wardLowGaugeMiddleWeight_eq_phase ϑ hCut κ hκ hSmall m w a ha hOdd hHom wi wo hm hη i o z k l j)
  have hInt : Integrable (radianTrilinearWeight M G (V l) (V j)) := hWeight.symm ▸ hInt₁.add hInt₂
  refine ⟨hInt, ?_⟩
  have hForm : radianTrilinearForm M G (V l) (V j) =
      radianTrilinearForm (wardLowRadialSymbol ϑ κ (fun y => (F y).1)) G (P l) (V j) +
      radianTrilinearForm (wardLowRadialSymbol ϑ κ (fun y => (F y).2)) G (V l) (P j) := by
    simp only [radianTrilinearForm, hWeight, integral_add' hInt₁ hInt₂, smul_add]
  have hn (f : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 f :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  rw [hForm]
  refine (norm_add_le _ _).trans ((add_le_add hB₁ hB₂).trans ?_)
  calc
    _ ≤ max C₁ C₂ * (wardCoordinateGradientL3 G * wardCoordinateGradientL3 (P l) * wardCoordinateGradientL3 (V j)) +
        max C₁ C₂ * (wardCoordinateGradientL3 G * wardCoordinateGradientL3 (V l) * wardCoordinateGradientL3 (P j)) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (mul_nonneg (hn G) (hn (P l))) (hn (V j))))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (mul_nonneg (hn G) (hn (V l))) (hn (P j))))
    _ = _ := by ring

end Burnett.C02
