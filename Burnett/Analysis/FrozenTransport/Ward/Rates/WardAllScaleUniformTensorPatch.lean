import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformActualBranches
import Mathlib.LinearAlgebra.Multilinear.Curry
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 22000000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.A05
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ContDiff Topology

open private wardMiddleTrilinear wardMiddleTrilinear_eq_symbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
open private wardMiddleTensorTrilinear wardMiddleTensorTrilinear_apply from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch

/-- All seven exact ordered tensor forms use one phase error bound on the
compact family, before the patch center, patch scale, or original field. -/
theorem exists_wardPhysicalPhaseTensor_compactPatchUniform
    (K V : Set E) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (m : E → Tensor2) (w : E → ℝ)
    (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => m x a b) V) (hw : ContDiffOn ℝ ∞ w V)
    (hSym : ∀ c ∈ K, IsSymmetricTensor (m c))
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ x ξ, a (x,-ξ) = -a (x,ξ))
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a (x,t • ξ) = t * a (x,ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E), c ∈ K → ∀ s : Fin 7,
      (∀ (wi wo : ℝ) (hs : WideScreenFrequencySmooth wi wo (m c)) (η : ℝ) (hη : 0 < η)
          (i o : ℝ) (z : ProjectionSchwartzMatrix),
        Integrable (wardActualTensorWeight (m c) (wardPhysicalPhaseSlots s)
          (wardPhysicalPhaseTensorSymbol ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) s)
          wi wo hs hη i o z)) ∧
      ∀ (wi wo : ℝ) (hs : WideScreenFrequencySmooth wi wo (m c)) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E)
        (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ Ce → 0 < ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let mass := ((volume : Measure E) P).toReal
      let M := mass ^ (1 / 3 : ℝ)
      let T := actualThinScreenMultiplier (m c) wi wo hs hη i o
      let diff (n : ℕ) (b : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
          multiplierCoordinateDerivative T (z n) b.1 b.2
      let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar (m c))
        (multiplierCoordinateDerivative T (z n) b.1 b.2)
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
      ∀ ε > 0, ∀ᶠ n in atTop,
        ‖wardActualTensorForm (m c) (wardPhysicalPhaseSlots s)
          (wardPhysicalPhaseTensorSymbol ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) s)
          wi wo hs hη i o (z n)‖ ≤ (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  classical
  let A (s : Fin 7) (c : E) := wardPhysicalPhaseTensorSymbol ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) s
  have hAll := wardActualPhaseComponents_compactFamilyUniform K V hK hV hKV m w hm hw a ha hOdd hHom
    ϑ hϑ hCut hFlat κ hκ hSmall
  have hStage (s : Fin 7) : WardFamilyComponentBounds K m (wardPhysicalPhaseSlots s)
      (fun k c x => A s c x (fun j => wardTensorBasis (k j))) := by
    fin_cases s
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![false,true,true] k
        (fun x => wardMiddleTensorTrilinear ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardMiddleTensorTrilinear_apply] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![false,true,true] k
        (fun x => wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardFirstLowTrilinear_apply, wardOneLowGaugeLieRawTrilinear_apply] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.2.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![true,true,false] k
        (fun x => wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardFirstLowTrilinear_apply, wardOneHighGaugeRawTrilinear_apply _ _ _ _ _ (hSym c hc)] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.2.2.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![true,false,false] k
        (fun x => wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardFirstLowTrilinear_apply, wardTwoGaugePhysicalRawTrilinear_apply] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.2.2.2.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![false,true,false] k
        (fun x => wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardFirstLowTrilinear_apply, wardTwoGaugeGaugeRawTrilinear_apply] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.2.2.2.2.1 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![true,true,false] k
        (fun x => wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardComparableTrilinear_apply, wardOneHighGaugeRawTrilinear_apply _ _ _ _ _ (hSym c hc)] using h c hc
    · intro k
      obtain ⟨C,hC,h⟩ := hAll.2.2.2.2.2.2 k
      refine ⟨C,hC,fun c hc => ?_⟩
      change WardActualLowComponentBound (m c) ![true,false,false] k
        (fun x => wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear (m c) (w c) (fun ξ => a (c,ξ))) x
          (fun j => wardTensorBasis (k j))) C
      simpa only [wardComparableTrilinear_apply, wardTwoGaugePhysicalRawTrilinear_apply] using h c hc
  choose C hC hB using hStage
  let D := ∑ s : Fin 7, ∑ k, C s k
  refine ⟨D, Finset.sum_nonneg (fun s _ => Finset.sum_nonneg fun k _ => hC s k), ?_⟩
  intro c hc s
  refine ⟨?_,?_⟩
  · intro wi wo hs η hη i o z
    exact (wardActualTensorForm_eq_sum (m c) (wardPhysicalPhaseSlots s) (A s c) (C s)
      (fun k => hB s k c hc) wi wo hs hη i o z).1
  intro wi wo hs η hη i o z P value grad Ce ell alpha hCe hEll hEll₁ hAlpha hv hSource mass M T diff phase hRate ε hε
  have hDom : ∑ k, C s k ≤ D :=
    Finset.single_le_sum (fun s _ => Finset.sum_nonneg fun k _ => hC s k) (Finset.mem_univ s)
  have h := wardActualTensorForm_patch_bound (m c) (wardPhysicalPhaseSlots s) (A s c) (C s)
    (hC s) (fun k => hB s k c hc) wi wo hs η hη i o z P value grad Ce ell alpha hCe hEll hEll₁ hAlpha hv hSource
    hRate ε hε
  filter_upwards [h] with n hn
  exact hn.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDom hCe)
      (sq_nonneg _)) (Real.rpow_nonneg hEll.le _)) ENNReal.toReal_nonneg) ε)

end Burnett.C02
