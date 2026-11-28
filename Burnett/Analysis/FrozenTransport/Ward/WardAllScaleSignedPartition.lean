import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransfer
import Burnett.Analysis.AllScaleTransfer.ActualUnscaledEstimate

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff BigOperators

open private wardExtendedTriadSymbol wardComparableSymbol_eq from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

private theorem wardTriadDomain_cycle_iff (x : Joint) : radianCycle x ∈ wardTriadDomain ↔ x ∈ wardTriadDomain := by
  have hThird : wardSignedThird (radianCycle x) = x.1 := by
    change -(x.2 + -(x.1+x.2)) = x.1
    abel
  change (x.2 ≠ 0 ∧ wardSignedThird x ≠ 0 ∧ wardSignedThird (radianCycle x) ≠ 0) ↔ _
  rw [hThird]
  exact ⟨fun h => ⟨h.2.2,h.1,h.2.1⟩, fun h => ⟨h.2.1,h.2.2,h.1⟩⟩

private theorem wardTriadDomain_cycle_symm_iff (x : Joint) : radianCycle.symm x ∈ wardTriadDomain ↔ x ∈ wardTriadDomain := by
  simpa only [MeasurableEquiv.apply_symm_apply] using (wardTriadDomain_cycle_iff (radianCycle.symm x)).symm

private theorem wardExtendedTriadSymbol_hom (F : Joint → ℂ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x) :
    ∀ t : ℝ, 0 < t → ∀ x : Joint, wardExtendedTriadSymbol F (t • x) = wardExtendedTriadSymbol F x := by
  classical
  intro t ht x
  have he : t • x ∈ wardTriadDomain ↔ x ∈ wardTriadDomain := by
    simp only [wardTriadDomain, mem_setOf_eq, wardSignedThird, Prod.smul_fst, Prod.smul_snd,
      ← smul_add, ← smul_neg, smul_ne_zero_iff_right ht.ne']
  by_cases hx : x ∈ wardTriadDomain
  · rw [wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ (he.mpr hx), piecewise_eq_of_mem _ _ _ hx, hHom t ht x hx]
  · rw [wardExtendedTriadSymbol, piecewise_eq_of_notMem _ _ _ (mt he.mp hx), piecewise_eq_of_notMem _ _ _ hx]
    rfl

private def normalizedComparableTriad (κ : ℝ) : Set Joint :=
  (closedBall (0 : E) (2 / κ) ×ˢ sphere (0 : E) 1) ∩
    {x | κ / 2 ≤ ‖x.1‖ ∧ κ / 2 ≤ ‖wardSignedThird x‖}

private theorem normalizedComparableTriad_compact (κ : ℝ) : IsCompact (normalizedComparableTriad κ) := by
  exact ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).inter_right
    ((isClosed_le continuous_const continuous_fst.norm).inter
      (isClosed_le continuous_const ((continuous_fst.add continuous_snd).neg.norm)))

private theorem normalizedComparableTriad_subset (κ : ℝ) (hκ : 0 < κ) :
    normalizedComparableTriad κ ⊆ wardTriadDomain := by
  intro y hy
  have hκ₂ : 0 < κ / 2 := by positivity
  exact ⟨norm_pos_iff.mp (hκ₂.trans_le hy.2.1),
    norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hy.1.2]; norm_num), norm_pos_iff.mp (hκ₂.trans_le hy.2.2)⟩

private theorem wardComparableSymbol_bounded (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : Joint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardTriadDomain)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖wardComparableSymbol ϑ κ F x‖ ≤ B := by
  classical
  let m := wardComparableSymbol ϑ κ F
  have hOn := ((wardComparableSymbol_smooth ϑ hϑ κ hκ.ne' F hF).continuousOn.mono
    (normalizedComparableTriad_subset κ hκ)).norm
  obtain ⟨B,hB⟩ := (normalizedComparableTriad_compact κ).bddAbove_image hOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x
  change ‖m x‖ ≤ max B 0
  by_cases hx : m x = 0
  · rw [hx,norm_zero]
    exact le_max_right _ _
  have hD : x ∈ wardTriadDomain := by
    by_contra h
    apply hx
    change wardComparableSymbol ϑ κ F x = 0
    rw [wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_notMem _ _ _ h, Pi.zero_apply, mul_zero]
  have hc : comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) ≠ 0 := by
    intro hr
    apply hx
    change wardComparableSymbol ϑ κ F x = 0
    rw [wardComparableSymbol_eq, hr, Complex.ofReal_zero, zero_mul]
  have b := comparableSlotWeight_signed_triad_bounds hCut hFlat hκ hSmall hD.2.1 hc
  let t := ‖x.2‖⁻¹
  have ht : 0 < t := inv_pos.mpr (norm_pos_iff.mpr hD.2.1)
  have hQ : t * ‖x.2‖ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD.2.1)
  have hNorm (p : E) : ‖t • p‖ = t * ‖p‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hThird : wardSignedThird (t • x) = t • wardSignedThird x := by
    simp only [wardSignedThird, Prod.smul_fst, Prod.smul_snd, smul_neg, smul_add]
  have hUpper : t * ‖x.1‖ ≤ 2 / κ := by
    apply (le_div_iff₀ hκ).mpr
    have hh := mul_le_mul_of_nonneg_left b.1.2 ht.le
    calc
      _ = 2 * (t * (κ / 2 * ‖x.1‖)) := by ring
      _ ≤ 2 * (t * ‖x.2‖) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by rw [hQ,mul_one]
  have hLower (p : E) (hp : κ / 2 * ‖x.2‖ ≤ ‖p‖) : κ / 2 ≤ t * ‖p‖ := by
    have hh := mul_le_mul_of_nonneg_left hp ht.le
    calc
      _ = t * (κ / 2 * ‖x.2‖) := by rw [mul_left_comm, hQ, mul_one]
      _ ≤ _ := hh
  have hK : t • x ∈ normalizedComparableTriad κ :=
    ⟨⟨mem_closedBall_zero_iff.mpr ((hNorm _).symm ▸ hUpper), mem_sphere_zero_iff_norm.mpr ((hNorm _).symm ▸ hQ)⟩,
      ⟨(hNorm _).symm ▸ hLower x.1 b.1.1, by rw [hThird,hNorm]; exact hLower _ b.2.1⟩⟩
  have he : m (t • x) = m x := radianFourBranchSymbol_homogeneous ϑ κ (wardExtendedTriadSymbol F)
    (wardExtendedTriadSymbol_hom F hHom) 3 t ht x
  rw [← he]
  exact (hB (mem_image_of_mem _ hK)).trans (le_max_left _ _)

private theorem wardLowActive_subset_triad : wardLowActive ⊆ wardTriadDomain := by
  intro x hx
  refine ⟨hx.1,hx.2.1,?_⟩
  intro h
  have he : x.1 = -x.2 := eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h)
  have hb := hx.2.2
  rw [he, norm_neg, div_self (norm_ne_zero_iff.mpr hx.2.1)] at hb
  norm_num at hb

private theorem wardLowSlotSymbol_eq_first (ϑ : ℝ → ℝ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (m : Joint → ℂ) (F : WardLowPoint → ℂ)
    (hAxis : ∀ x ∉ wardTriadDomain, m x = 0)
    (hMatch : ∀ x ∈ wardLowActive, m x = F (wardLowInput x)) :
    wardLowSlotSymbol ϑ κ F = radianFourBranchSymbol ϑ κ m 0 := by
  classical
  funext x
  change wardLowSlotSymbol ϑ κ F x = (lowSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) : ℂ) * m x
  by_cases hx : x ∈ wardLowActive
  · rw [wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx, hMatch x hx]
    rfl
  rw [wardLowSlotSymbol, piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]
  by_cases hD : x ∈ wardTriadDomain
  · have hLow : lowSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) = 0 := by
      by_contra hLow
      have hb := lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (x.1+x.2)) hD.2.1 hLow
      have ht := (div_le_iff₀ (norm_pos_iff.mpr hD.2.1)).mpr hb
      exact hx ⟨hD.1,hD.2.1,ht.trans_lt (by linarith only [hSmall])⟩
    rw [hLow, Complex.ofReal_zero, zero_mul]
  · rw [hAxis x hD, mul_zero]

/-- The actual bipolar Fourier measure and original four-branch frequency
partition can use the concrete low extensions of the same symbol. There
are no supplied box or chart estimates in this interface. -/
theorem exists_wardSignedPartitionForm_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : Joint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardTriadDomain)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x)
    (M : Fin 3 → WardLowPoint → ℂ) (hM : ∀ i, ContDiffOn ℝ ∞ (M i) wardLowProfileDomain)
    (hMatch : ∀ i x, x ∈ wardLowActive → radianLowSlotView F i x = M i (wardLowInput x)) :
    Measurable (wardExtendedTriadSymbol F) ∧
    (∃ B : ℝ, ∀ x, ‖wardExtendedTriadSymbol F x‖ ≤ B) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm (wardExtendedTriadSymbol F) f g h‖ ≤ C * (triLpMass f g h 3 3 3).toReal := by
  classical
  let m := wardExtendedTriadSymbol F
  have hMeas : Measurable m := hF.continuousOn.measurable_piecewise continuousOn_const wardTriadDomain_open.measurableSet
  have hAxis (i : Fin 3) (x : Joint) (hx : x ∉ wardTriadDomain) : radianLowSlotView m i x = 0 := by
    have h0 (y : Joint) (hy : y ∉ wardTriadDomain) : m y = 0 := by
      exact piecewise_eq_of_notMem _ _ _ hy
    fin_cases i
    · exact h0 x hx
    · exact h0 (radianCycle.symm x) (mt (wardTriadDomain_cycle_symm_iff x).mp hx)
    · exact h0 (radianCycle x) (mt (wardTriadDomain_cycle_iff x).mp hx)
  have hTrue (i : Fin 3) (x : Joint) (hx : x ∈ wardLowActive) :
      radianLowSlotView m i x = M i (wardLowInput x) := by
    have hD := wardLowActive_subset_triad hx
    have h0 (y : Joint) (hy : y ∈ wardTriadDomain) : m y = F y := piecewise_eq_of_mem _ _ _ hy
    have he (i : Fin 3) : radianLowSlotView m i x = radianLowSlotView F i x := by
      fin_cases i
      · exact h0 x hD
      · exact h0 (radianCycle.symm x) ((wardTriadDomain_cycle_symm_iff x).mpr hD)
      · exact h0 (radianCycle x) ((wardTriadDomain_cycle_iff x).mpr hD)
    exact (he i).trans (hMatch i x hx)
  have he (i : Fin 3) := wardLowSlotSymbol_eq_first ϑ hCut κ hκ hSmall
    (radianLowSlotView m i) (M i) (hAxis i) (hTrue i)
  have hu (x : WardLowPoint) (hp : ‖x.1‖ = 1) (hq : ‖x.2.1‖ = 1) (hρ : |x.2.2| < 1 / 3) :
      x ∈ wardLowProfileDomain := by
    refine ⟨by rw [hp]; norm_num, ?_, by rw [hq]; norm_num⟩
    rw [norm_smul,hp,mul_one,Real.norm_eq_abs]
    exact hρ.trans (by norm_num)
  have hlo (i : Fin 3) := exists_wardLowSlotForm_bound ϑ hϑ hCut κ hκ hSmall (M i) wardLowProfileDomain (hM i) hu
  choose B hB using (fun i => (hlo i).2.1)
  choose C hC hBound using (fun i => (hlo i).2.2)
  obtain ⟨B₃,_,hB₃⟩ := wardComparableSymbol_bounded ϑ hϑ hCut hFlat κ hκ hSmall F hF hHom
  obtain ⟨C₃,hC₃,hBound₃⟩ := exists_wardComparableForm_bound ϑ hϑ hCut hFlat κ hκ hSmall F hF hHom
  have hMbound (x : Joint) : ‖m x‖ ≤ B 0 + B 1 + B 2 + B₃ := by
    have hBounds (i : Fin 3) (y : Joint) : ‖radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0 y‖ ≤ B i :=
      he i ▸ hB i y
    have hOne : radianFourBranchSymbol ϑ κ m 1 x = radianFourBranchSymbol ϑ κ (radianLowSlotView m 1) 0 (radianCycle x) := by
      change _ = (lowSlotWeight ϑ κ x.2 (wardSignedThird x) (wardSignedThird (radianCycle x)) : ℂ) * m (radianCycle.symm (radianCycle x))
      have hThird : wardSignedThird (radianCycle x) = x.1 := by change -(x.2 + -(x.1+x.2)) = x.1; abel
      rw [hThird, MeasurableEquiv.symm_apply_apply]
      rfl
    have hTwo : radianFourBranchSymbol ϑ κ m 2 x = radianFourBranchSymbol ϑ κ (radianLowSlotView m 2) 0 (radianCycle.symm x) := by
      have hThird : wardSignedThird (radianCycle.symm x) = x.2 := by change -(-(x.1+x.2) + x.1) = x.2; abel
      change _ = (lowSlotWeight ϑ κ (wardSignedThird x) x.1 (wardSignedThird (radianCycle.symm x)) : ℂ) * m (radianCycle (radianCycle.symm x))
      rw [hThird, MeasurableEquiv.apply_symm_apply]
      rfl
    have hsum := (radianFourBranchSymbol_sum ϑ κ m x).symm
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_four]
    exact add_le_add (add_le_add (add_le_add (hBounds 0 x) (hOne.symm ▸ hBounds 1 (radianCycle x)))
      (hTwo.symm ▸ hBounds 2 (radianCycle.symm x))) (hB₃ x)
  refine ⟨hMeas, ⟨_,hMbound⟩, C 0 + C 1 + C 2 + C₃,
    add_nonneg (add_nonneg (add_nonneg (hC 0) (hC 1)) (hC 2)) hC₃,?_⟩
  intro f g h
  refine radianTrilinearForm_bound_of_four_branch_estimates ϑ hϑ.continuous.measurable hRange κ m hMeas _ hMbound f g h
    (C 0) (C 1) (C 2) C₃ ?_ ?_ ?_ (hBound₃ f g h)
  · exact he 0 ▸ hBound 0 f g h
  · exact he 1 ▸ hBound 1 g h f
  · exact he 2 ▸ hBound 2 h f g

end Burnett.C02
