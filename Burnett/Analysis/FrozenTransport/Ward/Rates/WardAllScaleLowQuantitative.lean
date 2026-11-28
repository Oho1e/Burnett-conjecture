import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransfer

set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 13500000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

open private wardLowActive_open wardLowInput_continuousOn wardLowSlotSymbol_of_active wardLowSlotSymbol_of_inactive wardUnitRatioCompact wardUnitRatioCompact_compact wardLowInput_mapsTo wardLowSlotSymbol_hom wardLowSlotSymbol_nonzero_ratio from Burnett.Analysis.FrozenTransport.Ward.WardLowTransfer

/-- Once the prescribed chart jet bound is supplied, the original
first-low constant is chosen before the coefficient or frozen center. -/
theorem exists_wardLowSlotForm_uniformBound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : WardLowPoint → ℂ) (U : Set WardLowPoint) (_hF : ContDiffOn ℝ ∞ F U)
      (_hU : ∀ x : WardLowPoint, ‖x.1‖ = 1 → ‖x.2.1‖ = 1 → |x.2.2| < 1 / 3 → x ∈ U)
      (D : ℝ), 0 ≤ D →
      let Φ := fun x => (wardLowNormalizedCutoff ϑ κ x : ℂ) * F x
      (∀ i, ContDiffOn ℝ 100 (Φ ∘ wardRatioChartLift i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4))) →
      (∀ i n, n ≤ 100 → ∀ x ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4),
        ‖iteratedFDerivWithin ℝ n (Φ ∘ wardRatioChartLift i)
          (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4)) x‖ ≤ D) →
      Measurable (wardLowSlotSymbol ϑ κ F) ∧ (∃ B : ℝ, ∀ x, ‖wardLowSlotSymbol ϑ κ F x‖ ≤ B) ∧
      ∀ f g h : SchwartzMap E ℂ,
        ‖radianTrilinearForm (wardLowSlotSymbol ϑ κ F) f g h‖ ≤ (C * D) * (triLpMass f g h 3 3 3).toReal := by
  classical
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
  refine ⟨C,hC,?_⟩
  intro F U hF hU D hD Φ hSmooth hJet
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (Complex.ofRealCLM.contDiff.comp (wardLowNormalizedCutoff_smooth ϑ hϑ κ hκ.ne')).contDiffOn.mul hF
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
  exact ⟨hMeas, ⟨max B 0,hBound⟩, applyBound (fun i => Φ ∘ wardRatioChartLift i)
    (fun x => Φ (x.1,x.2,0)) D hD hSmooth hJet hTrace
    (wardLowSlotSymbol ϑ κ F) (max B 0) (le_max_right _ _) hMeas hBound
    (wardLowSlotSymbol_hom ϑ κ F) (wardLowSlotSymbol_nonzero_ratio hCut hκ hSmall F) hChart⟩

/-- A family smooth on the receiving-center and independent-ratio
neighborhood has one original first-low multiplier bound. -/
theorem exists_wardLowSlotForm_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × WardLowPoint → ℂ) (U : Set WardLowPoint)
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ U))
    (hU : ∀ x : WardLowPoint, ‖x.1‖ = 1 → ‖x.2.1‖ = 1 → |x.2.2| < 1 / 3 → x ∈ U)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K,
      let A := wardLowSlotSymbol ϑ κ (fun z => F (c,z))
      Measurable A ∧ (∃ B : ℝ, ∀ x, ‖A x‖ ≤ B) ∧ ∀ f g h : SchwartzMap E ℂ,
        ‖radianTrilinearForm A f g h‖ ≤ C * (triLpMass f g h 3 3 3).toReal := by
  let Φ (z : X × WardLowPoint) := (wardLowNormalizedCutoff ϑ κ z.2 : ℂ) * F z
  have hΦ : ContDiffOn ℝ ∞ Φ (V ×ˢ U) :=
    (Complex.ofRealCLM.contDiff.comp ((wardLowNormalizedCutoff_smooth ϑ hϑ κ hκ.ne').comp
      contDiff_snd)).contDiffOn.mul hF
  obtain ⟨D,hD,hUniform⟩ := exists_wardRatioChartFamilyBudget K V hK hV hKV Φ U hΦ hU
  obtain ⟨C,hC,hBound⟩ := exists_wardLowSlotForm_uniformBound ϑ hϑ hCut κ hκ hSmall
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro c hc
  have hs : ContDiffOn ℝ ∞ (fun z => F (c,z)) U :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hKV hc,hz⟩)
  exact hBound _ U hs hU D hD (hUniform c hc).1 (hUniform c hc).2

end Burnett.C02
