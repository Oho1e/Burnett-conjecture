import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferCoordinates
import Burnett.Analysis.AngularCaps.SmoothCapProfiles

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

def wardLowActive : Set Joint :=
  {x | x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ ‖x.1‖ / ‖x.2‖ < 1 / 4}

def wardLowInput (x : Joint) : WardLowPoint :=
  (endpointDirection x.1, endpointDirection x.2, ‖x.1‖ / ‖x.2‖)

/-- The original signed first-low triad symbol, filled by zero where the
first-low frequency cut is zero. The third slot always has frequency `-(p+q)`. -/
def wardLowSlotSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (F : WardLowPoint → ℂ) : Joint → ℂ := by
  classical
  exact wardLowActive.piecewise (fun x =>
    (lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) * F (wardLowInput x)) 0

private theorem wardLowActive_open : IsOpen wardLowActive := by
  have hS : IsOpen {x : Joint | x.1 ≠ 0 ∧ x.2 ≠ 0} :=
    (isClosed_eq continuous_fst continuous_const).isOpen_compl.inter
      (isClosed_eq continuous_snd continuous_const).isOpen_compl
  have hR : ContinuousOn (fun x : Joint => ‖x.1‖ / ‖x.2‖) {x : Joint | x.1 ≠ 0 ∧ x.2 ≠ 0} :=
    continuous_fst.norm.continuousOn.div continuous_snd.norm.continuousOn
      (fun _ hx => norm_ne_zero_iff.mpr hx.2)
  have hSet : {x : Joint | x.1 ≠ 0 ∧ x.2 ≠ 0} ∩ (fun x => ‖x.1‖ / ‖x.2‖) ⁻¹' Iio (1 / 4 : ℝ) =
      wardLowActive := by
    ext x
    exact and_assoc
  exact hSet ▸ hR.isOpen_inter_preimage hS isOpen_Iio

private theorem wardLowInput_continuousOn : ContinuousOn wardLowInput wardLowActive := by
  apply ContinuousOn.prodMk
  · exact (endpointDirection_contDiffOn.continuousOn.comp continuous_fst.continuousOn fun _ hx => hx.1)
  · exact (endpointDirection_contDiffOn.continuousOn.comp continuous_snd.continuousOn fun _ hx => hx.2.1).prodMk
      (continuous_fst.norm.continuousOn.div continuous_snd.norm.continuousOn
        (fun _ hx => norm_ne_zero_iff.mpr hx.2.1))

private theorem wardLowSlotSymbol_of_active (ϑ : ℝ → ℝ) (κ : ℝ) (F : WardLowPoint → ℂ)
    (x : Joint) (hx : x ∈ wardLowActive) : wardLowSlotSymbol ϑ κ F x =
      (wardLowNormalizedCutoff ϑ κ (wardLowInput x) : ℂ) * F (wardLowInput x) := by
  classical
  rw [wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx]
  rw [wardLowInput, wardLowNormalizedCutoff_eq_lowSlotWeight ϑ κ x.1 x.2 hx.1 hx.2.1]

private theorem wardLowSlotSymbol_of_inactive (ϑ : ℝ → ℝ) (κ : ℝ) (F : WardLowPoint → ℂ)
    (x : Joint) (hx : x ∉ wardLowActive) : wardLowSlotSymbol ϑ κ F x = 0 := by
  classical
  rw [wardLowSlotSymbol, piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]

private theorem wardLowInput_smul (t : ℝ) (ht : 0 < t) (x : Joint) :
    wardLowInput (t • x) = wardLowInput x := by
  simp only [wardLowInput, Prod.smul_fst, Prod.smul_snd,
    endpointDirection_pos_smul t ht, norm_smul, Real.norm_of_nonneg ht.le,
    mul_div_mul_left _ _ ht.ne']

private theorem wardLowActive_smul_iff (t : ℝ) (ht : 0 < t) (x : Joint) :
    t • x ∈ wardLowActive ↔ x ∈ wardLowActive := by
  simp only [wardLowActive, mem_setOf_eq, Prod.smul_fst, Prod.smul_snd,
    norm_smul, Real.norm_of_nonneg ht.le, mul_div_mul_left _ _ ht.ne', smul_ne_zero_iff_right ht.ne']

private theorem wardLowSlotSymbol_hom (ϑ : ℝ → ℝ) (κ : ℝ) (F : WardLowPoint → ℂ)
    (t : ℝ) (ht : 0 < t) (x : Joint) : wardLowSlotSymbol ϑ κ F (t • x) = wardLowSlotSymbol ϑ κ F x := by
  by_cases hx : x ∈ wardLowActive
  · rw [wardLowSlotSymbol_of_active ϑ κ F _ ((wardLowActive_smul_iff t ht x).mpr hx),
      wardLowSlotSymbol_of_active ϑ κ F x hx, wardLowInput_smul t ht x]
  · rw [wardLowSlotSymbol_of_inactive ϑ κ F _ (mt (wardLowActive_smul_iff t ht x).mp hx),
      wardLowSlotSymbol_of_inactive ϑ κ F x hx]

private theorem wardLowSlotSymbol_nonzero_ratio {ϑ : ℝ → ℝ} (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    {κ : ℝ} (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : WardLowPoint → ℂ)
    (x : Joint) (hq : x.2 ≠ 0) (hNonzero : wardLowSlotSymbol ϑ κ F x ≠ 0) :
    ‖x.1‖ / ‖x.2‖ ≤ 2 * κ := by
  classical
  have hActive : x ∈ wardLowActive := by
    by_contra h
    exact hNonzero (wardLowSlotSymbol_of_inactive ϑ κ F _ h)
  have hLow : lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) ≠ 0 := by
    intro hZero
    apply hNonzero
    rw [wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hActive, hZero, Complex.ofReal_zero, zero_mul]
  exact (div_le_iff₀ (norm_pos_iff.mpr hq)).mpr
    (lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (x.1+x.2)) hq hLow)

private def wardUnitRatioCompact : Set WardLowPoint :=
  sphere (0 : E) 1 ×ˢ (sphere (0 : E) 1 ×ˢ Icc (0 : ℝ) (1 / 4))

private theorem wardUnitRatioCompact_compact : IsCompact wardUnitRatioCompact :=
  (isCompact_sphere _ _).prod ((isCompact_sphere _ _).prod isCompact_Icc)

private theorem wardLowInput_mapsTo : MapsTo wardLowInput wardLowActive wardUnitRatioCompact := by
  intro x hx
  exact ⟨endpointDirection_mem_sphere hx.1, endpointDirection_mem_sphere hx.2.1,
    div_nonneg (norm_nonneg _) (norm_nonneg _), hx.2.2.le⟩

/-- Every concrete smooth low-slot coefficient has an all-scale bound for
the same original first-low Fourier form. All finite angular charts and the
endpoint and derivative budgets are constructed here from the coefficient. -/
theorem exists_wardLowSlotForm_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (F : WardLowPoint → ℂ) (U : Set WardLowPoint) (hF : ContDiffOn ℝ ∞ F U)
    (hU : ∀ x : WardLowPoint, ‖x.1‖ = 1 → ‖x.2.1‖ = 1 → |x.2.2| < 1 / 3 → x ∈ U) :
    Measurable (wardLowSlotSymbol ϑ κ F) ∧
    (∃ B : ℝ, ∀ x, ‖wardLowSlotSymbol ϑ κ F x‖ ≤ B) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm (wardLowSlotSymbol ϑ κ F) f g h‖ ≤ C * (triLpMass f g h 3 3 3).toReal := by
  classical
  let Φ := fun x => (wardLowNormalizedCutoff ϑ κ x : ℂ) * F x
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (Complex.ofRealCLM.contDiff.comp (wardLowNormalizedCutoff_smooth ϑ hϑ κ hκ.ne')).contDiffOn.mul hF
  obtain ⟨D,hD,hSmooth,hJet⟩ := exists_wardRatioChartBudget Φ U hΦ hU
  have hKU : wardUnitRatioCompact ⊆ U := by
    intro x hx
    exact hU x (mem_sphere_zero_iff_norm.mp hx.1) (mem_sphere_zero_iff_norm.mp hx.2.1)
      (by rw [abs_of_nonneg hx.2.2.1]; exact hx.2.2.2.trans_lt (by norm_num))
  obtain ⟨B,hB⟩ := wardUnitRatioCompact_compact.bddAbove_image (hΦ.continuousOn.mono hKU).norm
  have hOn : EqOn (wardLowSlotSymbol ϑ κ F) (Φ ∘ wardLowInput) wardLowActive :=
    fun x hx => wardLowSlotSymbol_of_active ϑ κ F x hx
  have hOff : EqOn (wardLowSlotSymbol ϑ κ F) 0 wardLowActiveᶜ :=
    fun x hx => wardLowSlotSymbol_of_inactive ϑ κ F x hx
  have hMeas : Measurable (wardLowSlotSymbol ϑ κ F) := by
    have heq : wardLowSlotSymbol ϑ κ F = wardLowActive.piecewise (Φ ∘ wardLowInput) 0 := by
      funext x
      by_cases hx : x ∈ wardLowActive
      · rw [piecewise_eq_of_mem _ _ _ hx]
        exact hOn hx
      · rw [piecewise_eq_of_notMem _ _ _ hx]
        exact hOff hx
    rw [heq]
    exact ((hΦ.continuousOn.mono hKU).comp wardLowInput_continuousOn wardLowInput_mapsTo).measurable_piecewise
      continuousOn_const wardLowActive_open.measurableSet
  have hBound (x : Joint) : ‖wardLowSlotSymbol ϑ κ F x‖ ≤ max B 0 := by
    by_cases hx : x ∈ wardLowActive
    · rw [hOn hx]
      exact (hB (mem_image_of_mem _ (wardLowInput_mapsTo hx))).trans (le_max_left _ _)
    · rw [hOff hx, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hTrace (i : WardPairChart) (x : Joint) (hx : x ∈ wardPairChartAnnulus i) :
      Φ (endpointDirection x.1, endpointDirection x.2, 0) =
        (Φ ∘ wardRatioChartLift i) (wardPairChartAngles i x, 0) := by
    exact (congrArg Φ (wardRatioChartLift_angle i x hx 0)).symm
  have hChart (i : WardPairChart) (x : Joint) (hx : x ∈ wardPairChartAnnulus i) (t : ℝ) (ht : 0 < t)
      (hr : t * (‖x.1‖ / ‖x.2‖) ∈ Ioo (0 : ℝ) (1 / 4)) :
      wardLowSlotSymbol ϑ κ F (t • x.1,x.2) =
        (Φ ∘ wardRatioChartLift i) (wardPairChartAngles i x, t * (‖x.1‖ / ‖x.2‖)) := by
    have hann := wardPairChartAnnulus_subset i hx
    have hl : x.1 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hann.1.1)
    have hh : x.2 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hann.2.1)
    have hRatio : ‖t • x.1‖ / ‖x.2‖ = t * (‖x.1‖ / ‖x.2‖) := by
      rw [norm_smul, Real.norm_of_nonneg ht.le, mul_div_assoc]
    have ha : (t • x.1,x.2) ∈ wardLowActive :=
      ⟨smul_ne_zero ht.ne' hl, hh, hRatio.symm ▸ hr.2⟩
    rw [hOn ha, Function.comp_apply, Function.comp_apply, wardRatioChartLift_angle i x hx]
    simp only [wardLowInput, endpointDirection_pos_smul t ht, hRatio]
  let χ := descendingProfile κ (2 * κ)
  have hκu : κ < 2 * κ := by linarith only [hκ]
  have χRange (x : ℝ) (_ : 0 ≤ x) : ‖χ x‖ ≤ 1 := by
    have r := descendingProfile_range κ (2*κ) x
    rw [Real.norm_of_nonneg r.1]
    exact r.2
  obtain ⟨C,hC,applyBound⟩ := exists_unscaled_radian_firstLow_bound wardPairChartAnnulus
    wardPairChartDomain wardPairChartAngles wardPairChartAnnulus_open wardPairChartDomain_open
    wardPairChartAnnulus_covers wardPairChartAnnulus_subset wardPairChartAngles_smooth wardPairChartAngles_mapsTo
    κ (2 * κ) (1 / 4) hκ (by positivity) (by linarith only [hSmall]) (by linarith only [hSmall])
    χ (descendingProfile_contDiff _ _) χRange (fun _ _ h => descendingProfile_eq_one hκu h)
    (fun _ h => descendingProfile_eq_zero hκu h)
  exact ⟨hMeas, ⟨max B 0,hBound⟩, C * D, mul_nonneg hC hD, applyBound (fun i => Φ ∘ wardRatioChartLift i)
    (fun x => Φ (x.1,x.2,0)) D hD hSmooth hJet hTrace
    (wardLowSlotSymbol ϑ κ F) (max B 0) (le_max_right _ _) hMeas hBound
    (wardLowSlotSymbol_hom ϑ κ F) (wardLowSlotSymbol_nonzero_ratio hCut hκ hSmall F) hChart⟩

end Burnett.C02
