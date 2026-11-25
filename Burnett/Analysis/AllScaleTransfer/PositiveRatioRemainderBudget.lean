import Burnett.Analysis.AllScaleTransfer.PositiveRatioFTC
import Burnett.Analysis.AllScaleTransfer.FiniteRatioIntegralIoc
import Burnett.Analysis.AllScaleTransfer.LowRatioBounds

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.Analysis.LowRatio

open Set MeasureTheory
open scoped ContDiff Interval

/-- The full derivative budget for the actual ratio remainder on a positive
plateau of the original cutoff. Only continuity of M at ratio zero is
needed in this positive-window estimate. -/
theorem remainder_jets_on_positive_plateau {U : Set Angles} {b : ℝ} (hU : IsOpen U)
    (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    (hPlateau : ∀ r ∈ Ioo (0 : ℝ) b, χ r = 1)
    (hTrace : ContinuousOn M (U ×ˢ Ico (0 : ℝ) b))
    (hM : ContDiffOn ℝ 100 M (Window U 0 b)) (B : ℝ)
    (hBudget : ∀ n ≤ 100, ∀ z ∈ Window U 0 b, ‖iteratedFDeriv ℝ n M z‖ ≤ B) :
    ContDiffOn ℝ 99 (remainder M χ) (Window U 0 b) ∧
      ∀ n ≤ 99, ∀ z ∈ Window U 0 b, ‖iteratedFDeriv ℝ n (remainder M χ) z‖ ≤ B := by
  let D := Window U 0 b
  have hD : IsOpen D := hU.prod isOpen_Ioo
  let F := ratioDerivative M
  let u (t : ℝ) : Point → ℂ := F ∘ ratioScale t
  have hDeriv : ContDiffOn ℝ 99 (fderiv ℝ M) D := hM.fderiv_of_isOpen hD (by norm_num)
  have hF : ContDiffOn ℝ 99 F D := hDeriv.clm_apply contDiffOn_const
  have bF (j : ℕ) (hj : j ≤ 99) (z : Point) (hz : z ∈ D) :
      ‖iteratedFDeriv ℝ j F z‖ ≤ B := by
    have h := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ M) (c := ((0 : Angles), (1 : ℝ))) (hDeriv.contDiffAt (hD.mem_nhds hz))
      (show (j : WithTop ℕ∞) ≤ 99 by exact_mod_cast hj)
    have hDir : ‖((0 : Angles), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [hDir, one_mul, norm_iteratedFDeriv_fderiv] at h
    exact h.trans (hBudget (j+1) (by omega) z hz)
  have hSmooth (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : ContDiffOn ℝ 99 (u t) D :=
    (hF.comp_continuousLinearMap (ratioScale t)).mono (ratioScale_mapsTo_positiveWindow ht)
  have composeJet (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ 99)
      (z : Point) (hz : z ∈ D) :
      iteratedFDeriv ℝ j (u t) z =
        (iteratedFDeriv ℝ j F (ratioScale t z)).compContinuousLinearMap (fun _ => ratioScale t) := by
    have hPre := hD.preimage (ratioScale t).continuous
    have hz' := ratioScale_mapsTo_positiveWindow ht hz
    have hn : (j : WithTop ℕ∞) ≤ 99 := by exact_mod_cast hj
    change iteratedFDeriv ℝ j (F ∘ ratioScale t) z = _
    rw [← iteratedFDerivWithin_of_isOpen j hPre hz',
      (ratioScale t).iteratedFDerivWithin_comp_right hF hD.uniqueDiffOn hPre.uniqueDiffOn hz' hn,
      iteratedFDerivWithin_of_isOpen j hD hz']
  have hMeas (j : ℕ) (hj : j ≤ 99) (z : Point) (hz : z ∈ D) :
      ContinuousOn (fun t => iteratedFDeriv ℝ j (u t) z) (Ioc (0 : ℝ) 1) := by
    let A := ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) ℂ
    let L := Point →L[ℝ] Point
    let comp (w : (Fin j → L) × A) := w.2.compContinuousLinearMap w.1
    have hc : Continuous comp :=
      continuousOn_univ.mp (ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap
        (𝕜 := ℝ) (t := univ)).continuousOn
    have jetCont : ContinuousOn (iteratedFDeriv ℝ j F) D :=
      (hF.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hD.uniqueDiffOn).congr fun _ hw =>
        (iteratedFDerivWithin_of_isOpen j hD hw).symm
    have scaleCont : Continuous (fun t : ℝ => ratioScale t z) :=
      ratioScale_continuous.clm_apply continuous_const
    have hJ := jetCont.comp scaleCont.continuousOn
      (show MapsTo (fun t => ratioScale t z) (Ioc (0 : ℝ) 1) D from
        fun _ ht => ratioScale_mapsTo_positiveWindow ht hz)
    have hP : Continuous (fun t : ℝ => (fun _ : Fin j => ratioScale t)) :=
      continuous_pi fun _ => ratioScale_continuous
    refine (hc.continuousOn.comp (hP.continuousOn.prodMk hJ) (mapsTo_univ _ _)).congr ?_
    intro t ht
    exact composeJet t ht j hj z hz
  have uniform (j : ℕ) (hj : j ≤ 99) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
      (z : Point) (hz : z ∈ D) : ‖iteratedFDeriv ℝ j (u t) z‖ ≤ B := by
    rw [composeJet t ht j hj z hz]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hL := ratioScale_norm_le ⟨ht.1.le, ht.2⟩
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans
      (bF j hj _ (ratioScale_mapsTo_positiveWindow ht hz))
  obtain ⟨hAvg, _, bAvg⟩ := timeAverage_contDiffOn_and_jets_of_Ioc hD 99 u (fun _ => B)
    hSmooth hMeas uniform
  have eq : EqOn (remainder M χ) (timeAverage u) D := by
    intro z hz
    have boundFirst (x : Point) (hx : x ∈ D) : ‖ratioDerivative M x‖ ≤ B := by
      simpa only [norm_iteratedFDeriv_zero] using bF 0 (by decide) x hx
    rw [remainder_eq_integral_on_positive_plateau hU M χ hχ hTrace (hM.of_le (by norm_num))
      B boundFirst hz (hPlateau _ hz.2), timeAverage, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc]
    rfl
  refine ⟨hAvg.congr eq, ?_⟩
  intro j hj z hz
  rw [← iteratedFDerivWithin_of_isOpen j hD hz, iteratedFDerivWithin_congr eq hz j,
    iteratedFDerivWithin_of_isOpen j hD hz]
  exact bAvg j hj z hz

/-- Direct use of the manuscript's one-sided C100 input and derivative
budget up to the zero-ratio face. The actual annulus uses positive ratios. -/
theorem remainder_jets_of_oneSidedC100 {U : Set Angles} {b : ℝ} (hU : IsOpen U)
    (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    (hPlateau : ∀ r ∈ Ioo (0 : ℝ) b, χ r = 1)
    (hM : ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b)) (B : ℝ)
    (hBudget : ∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ B) :
    ContDiffOn ℝ 99 (remainder M χ) (Window U 0 b) ∧
      ∀ n ≤ 99, ∀ z ∈ Window U 0 b, ‖iteratedFDeriv ℝ n (remainder M χ) z‖ ≤ B := by
  let D := Window U 0 b
  let S := U ×ˢ Ico (0 : ℝ) b
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hDS : D ⊆ S := fun _ hz => ⟨hz.1, hz.2.1.le, hz.2.2⟩
  refine remainder_jets_on_positive_plateau hU M χ hχ hPlateau hM.continuousOn
    (hM.mono hDS) B ?_
  intro n hn z hz
  have hInt : S ∩ D = D := inter_eq_right.mpr hDS
  have h := hBudget n hn z (hDS hz)
  rw [← iteratedFDerivWithin_inter_open hD hz, hInt, iteratedFDerivWithin_of_isOpen n hD hz] at h
  exact h

end Burnett.Analysis.LowRatio
