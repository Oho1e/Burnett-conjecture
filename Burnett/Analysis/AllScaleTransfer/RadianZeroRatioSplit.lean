import Burnett.Analysis.AllScaleTransfer.RadianLowEndpointModes
import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionNormalized

set_option autoImplicit false
set_option maxHeartbeats 5800000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open scoped Topology

private theorem lowEndpointRadianWindows_eq_low_high {gap : ℕ} (hgap : 3 ≤ gap) (j : ℤ) (p : Joint) :
    lowEndpointRadianWindows gap j p =
      (radialLowCutoff ((2 : ℝ)^j / (2 : ℝ)^gap) p.1 : ℂ) * (integerRadialWindow j p.2 : ℂ) := by
  let r := (2 : ℝ)^j
  have hr : 0 < r := by unfold r; positivity
  let l := r / (2 : ℝ)^gap
  have hl : 0 < l := div_pos hr (by positivity)
  change (radialLowCutoff l p.1 : ℂ) * (integerRadialWindow j p.2 : ℂ) *
      (thickProductCutoff r (-(p.1+p.2)) : ℂ) =
        (radialLowCutoff l p.1 : ℂ) * (integerRadialWindow j p.2 : ℂ)
  by_cases h₁ : radialLowCutoff l p.1 = 0
  · simp only [h₁,Complex.ofReal_zero,zero_mul]
  by_cases h₂ : integerRadialWindow j p.2 = 0
  · simp only [h₂,Complex.ofReal_zero,mul_zero,zero_mul]
  have hn₁ : ‖p.1‖ ≤ r/4 := (le_of_lt (lt_of_not_ge (fun h => h₁ (radialLowCutoff_eq_zero hl h)))).trans
    (radialLowCutoff_scale_le hr hgap)
  have hn₂ := radialAnnularCutoff_nonzero hr h₂
  have hTri := norm_add_le p.1 p.2
  have hRev : ‖p.2‖ ≤ ‖p.1+p.2‖ + ‖p.1‖ := by
    have eq : p.1+p.2-p.1 = p.2 := by abel
    simpa only [eq] using norm_sub_le (p.1+p.2) p.1
  have hW : thickProductCutoff r (-(p.1+p.2)) = 1 := by
    refine thickProductCutoff_eq_one hr ?_ ?_ <;> rw [norm_neg] <;> linarith [hn₂.1,hn₂.2]
  rw [hW,Complex.ofReal_one,mul_one]

private theorem high_window_tsum_measurable_bound (F : ℤ → Joint → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hMeas : ∀ j, Measurable (F j)) (hNorm : ∀ j p, ‖F j p‖ ≤ B)
    (hZero : ∀ j p, integerRadialWindow j p.2 = 0 → F j p = 0) :
    Measurable (fun p => ∑' j, F j p) ∧ ∀ p, ‖∑' j, F j p‖ ≤ 3*B := by
  constructor
  · apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ)) (f := fun I p => ∑ j ∈ I, F j p)
    · intro I
      exact I.measurable_fun_sum (fun j _ => hMeas j)
    · rw [tendsto_pi_nhds]
      intro p
      obtain ⟨I,_,hI⟩ := exists_integerRadialWindow_support_card_le_three p.2
      have hSum : HasSum (fun j => F j p) (∑' j, F j p) :=
        (summable_of_ne_finset_zero (fun j hj => hZero j p (hI j hj))).hasSum
      exact hSum
  · intro p
    obtain ⟨I,hI,hz⟩ := exists_integerRadialWindow_support_card_le_three p.2
    rw [tsum_eq_sum (s := I) (fun j hj => hZero j p (hz j hj))]
    calc
      _ ≤ ∑ j ∈ I, B := norm_sum_le_of_le _ (fun j _ => hNorm j p)
      _ = (I.card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hB

theorem radianTrilinearForm_add {m n : Joint → ℂ} (f g h : SchwartzMap E ℂ)
    (hm : Integrable (radianTrilinearWeight m f g h)) (hn : Integrable (radianTrilinearWeight n f g h)) :
    radianTrilinearForm (fun p => m p+n p) f g h = radianTrilinearForm m f g h + radianTrilinearForm n f g h := by
  unfold radianTrilinearForm
  rw [← smul_add,← integral_add hm hn]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianTrilinearWeight,add_mul]

/-- Recombine the manuscript's zero-ratio term from its actual low-pass
and correction. Both sums use the same high annulus and complex Fourier
weight, and the low-pass sum retains its unchanged third thick window. -/
theorem radianTrilinearForm_zero_ratio_split (χ₀ : ℝ → ℝ) (hχ₀ : Measurable χ₀)
    (hχ : ∀ t ≥ 0, ‖χ₀ t‖ ≤ 1) (A : E ≃L[ℝ] E) (gap : ℕ) (hgap : 3 ≤ gap)
    (M₀ : Joint → ℂ) (hM₀ : Measurable M₀) (B : ℝ) (hB : 0 ≤ B) (hNorm : ∀ x, ‖M₀ x‖ ≤ B)
    (f g h : SchwartzMap E ℂ) :
    let endpoint (p : Joint) := radianEndpointAngular M₀ p.1 p.2 * (∑' j, lowEndpointRadianWindows gap j p)
    let correction (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ₀ A gap M₀ j p
    radianTrilinearForm (fun p => radianEndpointAngular M₀ p.1 p.2 *
      (χ₀ (‖A p.1‖ / ‖A p.2‖) : ℂ)) f g h =
      radianTrilinearForm endpoint f g h + radianTrilinearForm correction f g h := by
  intro endpoint correction
  let S (j : ℤ) (p : Joint) := radialLowCutoff ((2 : ℝ)^j / (2 : ℝ)^gap) p.1
  let D (j : ℤ) (p : Joint) := integerRadialWindow j p.2
  let M (p : Joint) := radianEndpointAngular M₀ p.1 p.2
  let c (p : Joint) := χ₀ (‖A p.1‖ / ‖A p.2‖)
  let W (j : ℤ) (p : Joint) := lowEndpointRadianWindows gap j p
  let Corr (j : ℤ) (p : Joint) := radianLowPassCorrectionBlock χ₀ A gap M₀ j p
  let L := SchwartzMap.seminorm ℝ 0 0 endpointHighProfile
  have hL : 0 ≤ L := by unfold L; positivity
  have hm : Measurable M := hM₀.comp ((measurable_fst.norm.inv.smul measurable_fst).prodMk
    (measurable_snd.norm.inv.smul measurable_snd))
  have hc : Measurable c := hχ₀.comp (((A.continuous.comp continuous_fst).norm.measurable).div
    ((A.continuous.comp continuous_snd).norm.measurable))
  have hcm (p : Joint) : ‖c p‖ ≤ 1 := hχ _ (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hs (j : ℤ) : Measurable (S j) := by
    unfold S radialLowCutoff
    exact ((radialBallBump.contDiff (n := 0)).continuous.comp (continuous_const.smul continuous_fst)).measurable
  have hsm (j : ℤ) (p : Joint) : ‖S j p‖ ≤ 1 := by
    unfold S radialLowCutoff
    rw [Real.norm_of_nonneg radialBallBump.nonneg]
    exact radialBallBump.le_one
  have hd (j : ℤ) : Measurable (D j) := by
    have e : D j = fun p => (endpointHighProfile ((2 : ℝ)^(-j) • p.2)).re := by
      funext p
      rw [endpointHighProfile_eq_integerRadialWindow,Complex.ofReal_re]
    rw [e]
    exact (Complex.continuous_re.comp (endpointHighProfile.continuous.comp
      (continuous_const.smul continuous_snd))).measurable
  have hdm (j : ℤ) (p : Joint) : ‖D j p‖ ≤ L := by
    have T := endpointHighProfile.norm_le_seminorm ℝ ((2 : ℝ)^(-j) • p.2)
    rwa [endpointHighProfile_eq_integerRadialWindow,Complex.norm_real] at T
  have eW (j : ℤ) (p : Joint) : W j p = (S j p : ℂ) * (D j p : ℂ) :=
    lowEndpointRadianWindows_eq_low_high hgap j p
  have eCorr (j : ℤ) (p : Joint) : Corr j p = M p * ((D j p : ℂ) * ((c p-S j p : ℝ) : ℂ)) := rfl
  obtain ⟨hW,hWb⟩ := high_window_tsum_measurable_bound W L hL
    (fun j => by
      have e := funext (eW j)
      rw [e]
      exact (Complex.continuous_ofReal.measurable.comp (hs j)).mul (Complex.continuous_ofReal.measurable.comp (hd j)))
    (fun j p => by
      rw [eW,norm_mul,Complex.norm_real,Complex.norm_real]
      exact (mul_le_mul (hsm j p) (hdm j p) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun j p e => by rw [eW]; change D j p = 0 at e; simp only [e,Complex.ofReal_zero,mul_zero])
  obtain ⟨hCorr,hCorrb⟩ := high_window_tsum_measurable_bound Corr (B*(L*2)) (by positivity)
    (fun j => by
      rw [funext (eCorr j)]
      exact hm.mul ((Complex.continuous_ofReal.measurable.comp (hd j)).mul
        (Complex.continuous_ofReal.measurable.comp (hc.sub (hs j)))))
    (fun j p => by
      rw [eCorr,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]
      have hh : ‖c p - S j p‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hcm p,hsm j p])
      exact mul_le_mul (hNorm _) (mul_le_mul (hdm j p) hh (norm_nonneg _) hL) (by positivity) hB)
    (fun j p e => by rw [eCorr]; change D j p = 0 at e; simp only [e,Complex.ofReal_zero,mul_zero,zero_mul])
  have he : Integrable (radianTrilinearWeight endpoint f g h) :=
    integrable_radianTrilinearWeight_of_bounded _ (hm.mul hW).aestronglyMeasurable (B*(3*L))
      (fun p => by
        rw [norm_mul]
        exact mul_le_mul (hNorm _) (hWb p) (norm_nonneg _) hB) f g h
  have hcorr : Integrable (radianTrilinearWeight correction f g h) :=
    integrable_radianTrilinearWeight_of_bounded _ hCorr.aestronglyMeasurable _ hCorrb f g h
  have axis : ∀ᵐ p ∂(volume : Measure Joint), p.2 ≠ (0 : E) := by
    have H : ∀ᵐ q ∂(volume : Measure E), q ≠ (0 : E) := by simp [ae_iff]
    rw [Measure.volume_eq_prod E E]
    exact (Measure.ae_prod_iff_ae_ae ((isOpen_ne_fun continuous_snd continuous_const).measurableSet)).2
      (Eventually.of_forall fun _ => H)
  have symbols : (fun p => M p * (c p : ℂ)) =ᵐ[volume] (fun p => endpoint p + correction p) := by
    filter_upwards [axis] with p hp
    obtain ⟨I,_,hI⟩ := exists_integerRadialWindow_support_card_le_three p.2
    have hDall : (∑ j ∈ I, D j p) = 1 := by
      have H := (integerRadialWindow_hasSum p.2).tsum_eq
      simpa only [if_neg hp,tsum_eq_sum (s := I) hI] using H
    have zW (j : ℤ) (hj : j ∉ I) : W j p = 0 := by rw [eW]; simp only [D,hI j hj,Complex.ofReal_zero,mul_zero]
    have zC (j : ℤ) (hj : j ∉ I) : Corr j p = 0 := by
      rw [eCorr]
      simp only [D,hI j hj,Complex.ofReal_zero,mul_zero,zero_mul]
    change M p * (c p : ℂ) = M p * (∑' j, W j p) + ∑' j, Corr j p
    rw [tsum_eq_sum (s := I) zW,tsum_eq_sum (s := I) zC,Finset.mul_sum,← Finset.sum_add_distrib]
    have ee (j : ℤ) : M p * W j p + Corr j p = (M p * (c p : ℂ)) * (D j p : ℂ) := by
      rw [eW,eCorr,Complex.ofReal_sub]
      ring
    simp_rw [ee]
    rw [← Finset.mul_sum,← Complex.ofReal_sum,hDall,Complex.ofReal_one,mul_one]
  have eForm : radianTrilinearForm (fun p => M p * (c p : ℂ)) f g h =
      radianTrilinearForm (fun p => endpoint p + correction p) f g h := by
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards [symbols] with p hp
    simp only [radianTrilinearWeight,hp]
  exact eForm.trans (radianTrilinearForm_add f g h he hcorr)

end Burnett.A05
