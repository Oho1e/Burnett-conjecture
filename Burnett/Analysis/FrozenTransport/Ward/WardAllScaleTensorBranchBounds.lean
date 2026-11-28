import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowLieTrilinear
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowBranches

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 15800000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Index Tensor2 IsSymmetricTensor)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ContDiff Topology

/-- Every entry of an ordered tensor form obeys the same specified physical
and gauge gradient budget, with its own fixed multiplier constant. -/
def WardTensorComponentBounds (m : Tensor2) (physical : Fin 3 → Bool) (A : Joint → WardTensorTrilinear) : Prop :=
  ∀ k : Fin 3 → OrderedPair, ∃ C : ℝ, 0 ≤ C ∧
    WardActualLowComponentBound m physical k (fun x => A x (fun j => wardTensorBasis (k j))) C

/-- The finite tensor realizations of all the low and comparable
physical-phase branches use the same actual C02 and C03 fields. -/
theorem wardAllScaleActualPhaseTensor_componentBounds (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (hm : IsSymmetricTensor m) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) :
    WardTensorComponentBounds m ![false,true,true] (wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a)) ∧
    WardTensorComponentBounds m ![true,true,false] (wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a)) ∧
    WardTensorComponentBounds m ![true,false,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a)) ∧
    WardTensorComponentBounds m ![false,true,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear m w a)) ∧
    WardTensorComponentBounds m ![true,true,false] (wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a)) ∧
    WardTensorComponentBounds m ![true,false,false] (wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a)) := by
  have hLow k := exists_wardActualLowBranchesComponent_bounds ϑ hϑ hCut κ hκ hSmall m w a ha hOdd hHom k
  have hComp k := exists_wardActualComparableGaugeComponent_bounds ϑ hϑ hCut hFlat κ hκ hSmall m w a ha hHom k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [wardFirstLowTrilinear_apply, wardOneLowGaugeLieRawTrilinear_apply] using (hLow k).1
  · intro k
    simpa only [wardFirstLowTrilinear_apply, wardOneHighGaugeRawTrilinear_apply _ _ _ _ _ hm] using (hLow k).2.1
  · intro k
    simpa only [wardFirstLowTrilinear_apply, wardTwoGaugePhysicalRawTrilinear_apply] using (hLow k).2.2.1
  · intro k
    simpa only [wardFirstLowTrilinear_apply, wardTwoGaugeGaugeRawTrilinear_apply] using (hLow k).2.2.2
  · intro k
    simpa only [wardComparableTrilinear_apply, wardOneHighGaugeRawTrilinear_apply _ _ _ _ _ hm] using (hComp k).1
  · intro k
    simpa only [wardComparableTrilinear_apply, wardTwoGaugePhysicalRawTrilinear_apply] using (hComp k).2

/-- From the actual branch multipliers, the tensor-valued Fourier form has
the original power of the patch scale and exactly one patch volume. -/
theorem exists_wardActualTensorForm_patch_bound (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (hA : WardTensorComponentBounds m physical A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
      (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ Ce → 0 < ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let mass := ((volume : Measure E) P).toReal
      let M := mass ^ (1 / 3 : ℝ)
      let T := actualThinScreenMultiplier m wi wo hm hη i o
      let diff (n : ℕ) (b : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
          multiplierCoordinateDerivative T (z n) b.1 b.2
      let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar m)
        (multiplierCoordinateDerivative T (z n) b.1 b.2)
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
      ∀ ε > 0, ∀ᶠ n in atTop, ‖wardActualTensorForm m physical A wi wo hm hη i o (z n)‖ ≤
        (K * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  classical
  choose C hC hBounds using hA
  exact ⟨∑ k, C k, Finset.sum_nonneg fun k _ => hC k, fun wi wo hm η hη i o z P value grad Ce ell alpha =>
    wardActualTensorForm_patch_bound m physical A C hC hBounds wi wo hm η hη i o z P value grad Ce ell alpha⟩

end Burnett.C02
