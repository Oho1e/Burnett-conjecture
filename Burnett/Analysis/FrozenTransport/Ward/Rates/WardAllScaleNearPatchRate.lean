import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualGradient
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScalePhasePatchSum
import Burnett.Analysis.AllScaleTransfer.ActualFieldRadialLimit
import Burnett.Analysis.TransportPatches.PatchProjectedLpScale

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 12600000

noncomputable section

namespace Burnett.C02

open Set Filter Metric MeasureTheory
open Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ENNReal Topology

open private schwartzFieldLp3_norm_le_sum from Burnett.Analysis.AllScaleTransfer.ActualFieldRadialLimit

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The original near term of the frozen cubic decomposition, with its
original radian Fourier integration factor. -/
def wardActualNearCubicForm (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ}
    (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) : ℂ :=
  let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
  ((tau^8)⁻¹ : ℝ) • ∫ x, (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight G a H H H x

theorem wardActualNearCubicForm_eq_gradientSum (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ}
    (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix)
    (hInt : ∀ j : WardNearEntries, Integrable
      (radianTrilinearWeight (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j)
        (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2))) :
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    Integrable (fun x => (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight G a H H H x) ∧
      wardActualNearCubicForm G a ϑ κ δ wi wo hm hη i o z =
        ∑ j : WardNearEntries, radianTrilinearForm (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j)
          (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2) := by
  intro H
  let M (j : WardNearEntries) := radianTrilinearWeight (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j)
    (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2)
  have h := funext (wardActualNearWeight_eq_gradientSum G hG a ϑ κ δ wi wo hm hη i o z)
  have h' : (fun x => (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight G a H H H x) =
      (fun x => ∑ j, M j x) := h
  refine ⟨h'.symm ▸ integrable_finset_sum Finset.univ (fun j _ => hInt j),?_⟩
  change ((tau^8)⁻¹ : ℝ) • (∫ x, (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
    wardCyclicCubicWeight G a H H H x) = ∑ j, ((tau^8)⁻¹ : ℝ) • (∫ x, M j x)
  rw [h',← Finset.smul_sum,← integral_finset_sum Finset.univ (fun j _ => hInt j)]

/-- The derivative input of the near form uses the actual physical
projection in C03 and its exact patch-volume normalization. -/
theorem wardNearGradient_fieldL3_le (z : ProjectionSchwartzMatrix) (P : Set E) (value grad : ℝ)
    (h : ProjectedPatchLpBounds 3 z P value grad) :
    ‖schwartzFieldLp3 (wardNearGradient z)‖ ≤
      (Fintype.card WardNearSlot : ℝ) * grad * ((volume : Measure E) P).toReal ^ (1/3 : ℝ) := by
  have hTerm (j : WardNearSlot) : ‖(wardNearGradient z j).toLp (ENNReal.ofReal 3) volume‖ ≤
      grad * ((volume : Measure E) P).toReal ^ (1/3 : ℝ) := by
    rw [SchwartzMap.norm_toLp,ENNReal.toReal_rpow]
    exact ((h j.1.1 j.1.2).2 j.2).1
  calc
    _ ≤ ∑ j : WardNearSlot, ‖(wardNearGradient z j).toLp (ENNReal.ofReal 3) volume‖ :=
      schwartzFieldLp3_norm_le_sum _
    _ ≤ ∑ _j : WardNearSlot, grad * ((volume : Measure E) P).toReal ^ (1/3 : ℝ) :=
      Finset.sum_le_sum fun j _ => hTerm j
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

/-- Cubing the three actual gradient factors restores exactly one copy
of the original patch volume. -/
theorem wardActualNear_patch_rate_of_fieldL3 (z : ProjectionSchwartzMatrix) (P : Set E)
    (N : ℂ) (value grad C δ β : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (h : ProjectedPatchLpBounds 3 z P value grad)
    (hNear : ‖N‖ ≤ C*δ^β*‖schwartzFieldLp3 (wardNearGradient z)‖^3) :
    ‖N‖ ≤ C*((Fintype.card WardNearSlot : ℝ)*grad)^3*δ^β*((volume : Measure E) P).toReal := by
  let V := ((volume : Measure E) P).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hCube : (V^(1/3 : ℝ))^3 = V := by
    rw [← Real.rpow_natCast (V^(1/3 : ℝ)) 3, ← Real.rpow_mul hV]
    norm_num
  calc
    _ ≤ C*δ^β*(((Fintype.card WardNearSlot : ℝ)*grad)*V^(1/3:ℝ))^3 :=
      hNear.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (wardNearGradient_fieldL3_le z P value grad h) 3)
        (mul_nonneg hC (Real.rpow_nonneg hδ _)))
    _ = _ := by rw [mul_pow,hCube]; ring

/-- Fixed common C03 cutoffs give the original near decay with no
additional patch-scale loss and the same original overlap used by C04. -/
theorem wardActualNear_sum_originalPatchFamily
    (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (K : Set E) (hK : IsCompact K)
    (hPatch : ∀ j ∈ s, closedBall (patchCenter ℓ j) (6*ℓ) ⊆ K)
    (Z : LatticeIndex → ℕ → ProjectionSchwartzMatrix) (N : LatticeIndex → ℕ → ℂ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (Cp C δ β : ℝ)
    (hCp : 0 ≤ Cp) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRaw : ∀ j ∈ s, ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (Z j n)
      (closedBall (patchCenter ℓ j) (6*ℓ)) (Cp*e n) (Cp*(1+e n/ℓ)))
    (hEstimate : ∀ j ∈ s, ∀ n, ‖N j n‖ ≤ C*δ^β*‖schwartzFieldLp3 (wardNearGradient (Z j n))‖^3) :
    ∀ ε > 0, ∀ᶠ n in atTop, (∑ j ∈ s, ‖N j n‖) ≤
      (17^4 : ℝ)*C*((Fintype.card WardNearSlot : ℝ)*(2*Cp))^3*δ^β*((volume : Measure E) K).toReal + ε := by
  let Cnear := C*((Fintype.card WardNearSlot : ℝ)*(2*Cp))^3*δ^β
  have hCnear : 0 ≤ Cnear := by
    exact mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ (Fintype.card WardNearSlot : ℝ)*(2*Cp)) _))
      (Real.rpow_nonneg hδ _)
  have hSmall : ∀ᶠ n in atTop, e n ≤ ℓ := ((tendsto_order.1 he).2 ℓ hℓ).mono (fun _ hn => hn.le)
  have hRate := wardPhysicalPhase_sum_scaled_patch s ℓ hℓ K hK hPatch N Cnear 0 hCnear
  simp only [Real.rpow_zero,mul_one] at hRate
  have hPoint (j : LatticeIndex) (hj : j ∈ s) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ‖N j n‖ ≤ Cnear * ((volume : Measure E) (closedBall (patchCenter ℓ j) (6*ℓ))).toReal + ε := by
    filter_upwards [hRaw j hj,hSmall] with n hn hs
    have hCut : Cp*(1+e n/ℓ) ≤ 2*Cp := by
      have e' := mul_le_mul_of_nonneg_left (add_le_add_left ((div_le_one hℓ).mpr hs) 1) hCp
      linarith only [e']
    exact (wardActualNear_patch_rate_of_fieldL3 (Z j n) _ (N j n) (Cp*e n) (2*Cp) C δ β
      hC hδ (hn.mono le_rfl hCut) (hEstimate j hj n)).trans (le_add_of_nonneg_right hε.le)
  intro ε hε
  filter_upwards [hRate hPoint ε hε] with n hn
  have e' : (17^4 : ℝ)*Cnear*((volume : Measure E) K).toReal =
      (17^4 : ℝ)*C*((Fintype.card WardNearSlot : ℝ)*(2*Cp))^3*δ^β*((volume : Measure E) K).toReal := by
    unfold Cnear
    ring
  rw [e'] at hn
  exact hn

end Burnett.C02
