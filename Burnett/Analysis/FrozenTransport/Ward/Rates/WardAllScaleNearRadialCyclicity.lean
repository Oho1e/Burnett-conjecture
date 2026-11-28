import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearSymbolStructure
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearEndpointBudgets
import Burnett.Analysis.AllScaleTransfer.ActualNearCapDecomposition
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

set_option autoImplicit false
set_option maxRecDepth 8400
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.CapFourier

open private lowSlotWeight_smul from Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

def wardNearRotateEntries (k : Fin 3) (j : WardNearEntries) : WardNearEntries :=
  ![j,wardNearCycleEntries (wardNearCycleEntries j),wardNearCycleEntries j] k

def wardNearRotateCap (k : Fin 3) : Fin 3 := ![0,2,1] k

private theorem wardRadianCycle_symm_eq_cycle_sq (x : Joint) :
    radianCycle.symm x = radianCycle (radianCycle x) := by
  apply Prod.ext
  · rfl
  · change x.1 = -(x.2 + -(x.1+x.2))
    abel

/-- Reordering a true low frequency preserves the old designated base-cap
slot and permutes the original tensor derivative words with the same cycle. -/
theorem wardNear_rotatedCapCore_eq (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o capIn capOut capWide D : ℝ)
    (S : SmoothThinConeCaps (inverseMatrix G) δ η capIn capOut capWide D) (γ : ↑S.centers)
    (j : WardNearEntries) (k : Fin 3) (y : Joint) :
    let m := wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (m j) γ : Joint → ℂ)
    let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
    let P := capMultiplier S.centers (inverseMatrix G) δ η capIn capOut γ
    let slots : Fin 3 → E := ![y.1,y.2,-(y.1+y.2)]
    bases k y = ((δ^2)⁻¹ : ℝ) • ((P (slots (wardNearRotateCap k)) : ℂ) * m (wardNearRotateEntries k j) y) := by
  intro m μ bases P slots
  fin_cases k
  · rfl
  · change μ (radianCycle.symm y) = ((δ^2)⁻¹ : ℝ) •
      ((P (-(y.1+y.2)) : ℂ) * m (wardNearCycleEntries (wardNearCycleEntries j)) y)
    change ((δ^2)⁻¹ : ℝ) • ((P (-(y.1+y.2)) : ℂ) * m j (radianCycle.symm y)) = _
    rw [wardRadianCycle_symm_eq_cycle_sq]
    dsimp only [m]
    rw [wardNearGradientSymbol_cycle G a ϑ κ δ wi wo hm hη i o]
    rw [wardNearGradientSymbol_cycle G a ϑ κ δ wi wo hm hη i o]
  · change ((δ^2)⁻¹ : ℝ) • ((P y.2 : ℂ) * m j (radianCycle y)) =
      ((δ^2)⁻¹ : ℝ) • ((P y.2 : ℂ) * m (wardNearCycleEntries j) y)
    dsimp only [m]
    rw [wardNearGradientSymbol_cycle G a ϑ κ δ wi wo hm hη i o]

/-- The actual first-low branch evaluated at a common positive radial
scale equals the same localized differentiated symbol at unit high
parabolic radius, with its original cap placement. -/
theorem wardNear_rotatedLowBranch_normalize (G : Mat) (hG : Matrix.det G ≠ 0) (a : E → ℝ)
    (ha : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t*a ξ)
    (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o capIn capOut capWide D : ℝ)
    (S : SmoothThinConeCaps (inverseMatrix G) δ η capIn capOut capWide D) (γ : ↑S.centers)
    (j : WardNearEntries) (k : Fin 3) (t : ℝ) (ht : 0 < t) (z : Joint) :
    let m := wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (m j) γ : Joint → ℂ)
    let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
    let P := capMultiplier S.centers (inverseMatrix G) δ η capIn capOut γ
    let r := -(z.1+z.2)
    let slots : Fin 3 → E := ![z.1,z.2,r]
    let y : Joint := t • z
    radianFourBranchSymbol ϑ κ (bases k) 0 y =
      ((δ^2)⁻¹ : ℝ) • ((P (slots (wardNearRotateCap k)) : ℂ) *
        (lowSlotWeight ϑ κ z.1 z.2 r : ℂ) * m (wardNearRotateEntries k j) z) := by
  intro m μ bases P r slots y
  have hBase := wardNear_rotatedCapCore_eq G a ϑ κ δ wi wo hm hη i o capIn capOut capWide D S γ j k y
  change bases k y = ((δ^2)⁻¹ : ℝ) •
    ((P (![y.1,y.2,-(y.1+y.2)] (wardNearRotateCap k)) : ℂ) * m (wardNearRotateEntries k j) y) at hBase
  have hr : -(t • z.1+t • z.2) = t • r := by change _ = t • (-(z.1+z.2)); rw [smul_neg,smul_add]
  have hSlot (s : Fin 3) : (![y.1,y.2,-(y.1+y.2)] s : E) = t • slots s := by
    fin_cases s
    · rfl
    · rfl
    · exact hr
  rw [hSlot] at hBase
  have hCap : P (t • slots (wardNearRotateCap k)) = P (slots (wardNearRotateCap k)) :=
    capMultiplier_degreeZero S.centers _ δ η capIn capOut γ t ht.ne' _
  have hM := wardNearGradientSymbol_homogeneous G hG a ha ϑ κ δ wi wo hm hη i o (wardNearRotateEntries k j) t ht z
  change m (wardNearRotateEntries k j) y = m (wardNearRotateEntries k j) z at hM
  rw [hCap,hM] at hBase
  change (lowSlotWeight ϑ κ (t • z.1) (t • z.2) (-(t • z.1+t • z.2)) : ℂ) * bases k y = _
  rw [hr,lowSlotWeight_smul ϑ κ t ht,hBase]
  simp only [Complex.real_smul]
  ring

private theorem wardEndpointDirection_norm (p : E) (hp : p ≠ 0) :
    ‖endpointDirection p‖ = 1 := by
  unfold endpointDirection
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]

/-- Relate the actual A05 physical ratio to the exact joint common
parabolic coordinates, including the homogeneity factor in both slots. -/
theorem wardNear_normalizeEndpointRatio {m : Form} {w : E} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) {p q : E} (hp : p ≠ 0) (hq : q ≠ 0) :
    let A := capFrequencyEquiv F hδ
    let u := endpointDirection p
    let v := endpointDirection q
    let R := ‖p‖/‖q‖
    let y : Joint := (A p,A q)
    let z : Joint := (A (R • u),A v)
    0 < R ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ y = ‖q‖ • z ∧
      wardParabolicRatioOfPhysical F.toFrequency.toContinuousLinearMap δ (frequencyCoordinates u)
        (frequencyCoordinates v) (‖A p‖/‖A q‖) = R := by
  intro A u v R y z
  have hpN := norm_pos_iff.mpr hp
  have hqN := norm_pos_iff.mpr hq
  have hR : 0 < R := div_pos hpN hqN
  have hV (x : E) (hx : x ≠ 0) : ‖x‖ • endpointDirection x = x := by
    rw [endpointDirection,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
  have e₀ : ‖q‖ • (R • u) = p := by
    rw [smul_smul,show ‖q‖*R = ‖p‖ from mul_comm ‖q‖ R |>.trans (div_mul_cancel₀ ‖p‖ hqN.ne')]
    exact hV p hp
  have e₁ : ‖q‖ • v = q := hV q hq
  have hY : y = ‖q‖ • z := by
    apply Prod.ext
    · change A p = ‖q‖ • A (R • u)
      rw [← map_smul,e₀]
    · change A q = ‖q‖ • A v
      rw [← map_smul,e₁]
  have hAu : A u ≠ 0 := by
    intro h
    have hu := A.injective (h.trans A.map_zero.symm)
    change endpointDirection p = 0 at hu
    exact hp (by simpa only [hu,smul_zero] using (hV p hp).symm)
  have hAv : A v ≠ 0 := by
    intro h
    have hv := A.injective (h.trans A.map_zero.symm)
    change endpointDirection q = 0 at hv
    exact hq (by simpa only [hv,smul_zero] using (hV q hq).symm)
  have hNorm : ‖A p‖/‖A q‖ = ‖R • A u‖/‖A v‖ := by
    have e := congrArg Prod.fst hY
    have e' := congrArg Prod.snd hY
    change A p = ‖q‖ • A (R • u) at e
    change A q = ‖q‖ • A v at e'
    calc
      _ = (‖q‖*‖A (R • u)‖)/(‖q‖*‖A v‖) := by
        rw [e,e']
        simp only [norm_smul,Real.norm_of_nonneg hqN.le]
      _ = _ := by rw [mul_div_mul_left _ _ hqN.ne',map_smul]
  refine ⟨hR,wardEndpointDirection_norm p hp,wardEndpointDirection_norm q hq,hY,?_⟩
  rw [hNorm]
  exact wardParabolicRatioOfPhysical_eq F.toFrequency.toContinuousLinearMap δ
    (frequencyCoordinates u) (frequencyCoordinates v) R hR.le hAu hAv

end Burnett.C02
