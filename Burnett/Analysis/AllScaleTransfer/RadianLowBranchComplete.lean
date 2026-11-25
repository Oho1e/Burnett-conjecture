import Burnett.Analysis.AllScaleTransfer.RadianLowBranchAssembly
import Burnett.Analysis.AllScaleTransfer.RadianRemainderGapSplit

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps

/-- The actual low-slot cutoff keeps the physical ratio strictly inside
the open end of the atlas at twice the separation parameter. -/
theorem lowSlotWeight_nonzero_ratio_margin
    {ϑ : ℝ → ℝ} (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1/16)
    {p q r : E} (hTriad : p + q + r = 0) (hq : q ≠ 0)
    (hLow : lowSlotWeight ϑ κ p q r ≠ 0) : ‖p‖ < (7*κ/4)*‖q‖ := by
  have nq := norm_pos_iff.mpr hq
  have hDen : 0 < κ^2*(‖q‖^2+‖r‖^2) :=
    mul_pos (pow_pos hκ _) (add_pos_of_pos_of_nonneg (pow_pos nq _) (sq_nonneg _))
  have hCut' : ‖p‖^2/(κ^2*(‖q‖^2+‖r‖^2)) < 1 :=
    lt_of_not_ge fun hn => hLow (hCut _ hn)
  have hSmall := (div_lt_iff₀ hDen).mp hCut'
  have hp := lowSlotWeight_nonzero_small hCut hκ hκ' hTriad hq hLow
  have hp' : (2*κ)*‖q‖ ≤ (1/8)*‖q‖ :=
    mul_le_mul_of_nonneg_right (by linarith only [hκ']) nq.le
  have hr : ‖r‖ ≤ (9/8)*‖q‖ := by
    linarith only [(high_norm_diff_of_triad hTriad).2, hp.trans hp']
  have hr2 := pow_le_pow_left₀ (norm_nonneg r) hr 2
  have hDen' := mul_le_mul_of_nonneg_left
    (add_le_add_left hr2 (‖q‖^2)) (sq_nonneg κ)
  have hStrength : κ^2*(‖q‖^2+((9/8)*‖q‖)^2) < ((7*κ/4)*‖q‖)^2 := by
    have hPositive : 0 < (κ*‖q‖)^2 := pow_pos (mul_pos hκ nq) 2
    nlinarith only [hPositive]
  have hp2 : ‖p‖^2 < ((7*κ/4)*‖q‖)^2 := by
    exact (by simpa only [one_mul] using hSmall :
      ‖p‖^2 < κ^2*(‖q‖^2+‖r‖^2)).trans_le hDen' |>.trans hStrength
  by_contra! h
  exact (not_le_of_gt hp2)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (7*κ/4)*‖q‖) h 2)

/-- The raw remainder is represented by zero on the zero-high-frequency
axis. Its trilinear form is unchanged. -/
def radianFirstLowRemainder (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (p : Joint) : ℂ :=
  if p.2 = 0 then 0 else radianRatioRemainderSymbol χ₀ A M₀ m p

/-- The original low form splits into its low-pass term, cutoff correction,
large-gap tail and finite signed-shift terms on the same Fourier inputs. -/
theorem exists_radianTrilinearForm_first_low_gap_decomposition (R : ℝ) (hR : 0 < R) :
    ∃ H : ℕ, ∀ (χ₀ : ℝ → ℝ) (_ : Measurable χ₀) (_ : ∀ t ≥ 0, ‖χ₀ t‖ ≤ 1)
      (A : E ≃L[ℝ] E) (gap cutoff : ℕ) (_ : 3 ≤ gap) (m M₀ : Joint → ℂ),
      Measurable m → Measurable M₀ → ∀ B B₀ : ℝ, 0 ≤ B → 0 ≤ B₀ →
      (∀ p, ‖m p‖ ≤ B) → (∀ p, ‖M₀ p‖ ≤ B₀) →
      (∀ p, p.2 ≠ 0 → radianRatioRemainderSymbol χ₀ A M₀ m p ≠ 0 →
        ‖p.1‖ ≤ R * ‖p.2‖) →
      ∀ f g h : SchwartzMap E ℂ,
      let L (p : Joint) := radianEndpointAngular M₀ p.1 p.2 * ∑' j, lowEndpointRadianWindows gap j p
      let D (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ₀ A gap M₀ j p
      let rem := radianFirstLowRemainder χ₀ A M₀ m
      let T (s : {s : ℕ // cutoff ≤ s}) :=
        radianTrilinearForm (radianLowGapSymbol rem s.val) f g h
      Summable T ∧ radianTrilinearForm m f g h =
        radianTrilinearForm L f g h + radianTrilinearForm D f g h +
          ((∑' s, T s) + ∑ k ∈ Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ),
            radianTrilinearForm (radianSignedGapSymbol rem k) f g h) := by
  obtain ⟨H, hGapAssembly⟩ := exists_radianTrilinearForm_remainder_gap_split R hR
  refine ⟨H, ?_⟩
  intro χ₀ hχ₀ hχ A gap cutoff hgap m M₀ hm hM₀ B B₀ hB hB₀ hNorm hNorm₀ hSupport f g h L D rem T
  let M (p : Joint) := radianEndpointAngular M₀ p.1 p.2
  let c (p : Joint) := χ₀ (‖A p.1‖ / ‖A p.2‖)
  have hM : Measurable M := hM₀.comp
    ((measurable_fst.norm.inv.smul measurable_fst).prodMk (measurable_snd.norm.inv.smul measurable_snd))
  have hc : Measurable c := hχ₀.comp
    ((A.continuous.comp continuous_fst).norm.measurable.div
      (A.continuous.comp continuous_snd).norm.measurable)
  have hz : IsOpen {p : Joint | p.2 ≠ (0 : E)} := isOpen_ne_fun continuous_snd continuous_const
  have hRem : Measurable rem :=
    Measurable.ite (isClosed_eq continuous_snd continuous_const).measurableSet measurable_const
      (hm.sub (hM.mul (Complex.continuous_ofReal.measurable.comp hc)))
  have hRemNorm (p : Joint) : ‖rem p‖ ≤ B+B₀ := by
    by_cases e : p.2 = 0
    · simpa only [rem, radianFirstLowRemainder, if_pos e, norm_zero] using add_nonneg hB hB₀
    · change ‖radianFirstLowRemainder χ₀ A M₀ m p‖ ≤ _
      rw [radianFirstLowRemainder, if_neg e]
      change ‖m p - M p * (c p : ℂ)‖ ≤ _
      refine (norm_sub_le _ _).trans (add_le_add (hNorm p) ?_)
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_mul (hNorm₀ _) (hχ _ (div_nonneg (norm_nonneg _) (norm_nonneg _)))
        (norm_nonneg _) hB₀).trans_eq (mul_one _)
  have hRemSupport (p : Joint) (hp : rem p ≠ 0) : ‖p.1‖ ≤ R * ‖p.2‖ := by
    have e : p.2 ≠ 0 := fun z => hp (by simp [rem, radianFirstLowRemainder, z])
    exact hSupport p e (by simpa only [rem, radianFirstLowRemainder, if_neg e] using hp)
  have hEqual : radianTrilinearForm (radianRatioRemainderSymbol χ₀ A M₀ m) f g h =
      radianTrilinearForm rem f g h := by
    have axis : ∀ᵐ p ∂(volume : Measure Joint), p.2 ≠ (0 : E) := by
      have hq : ∀ᵐ q ∂(volume : Measure E), q ≠ (0 : E) := by simp [ae_iff]
      rw [Measure.volume_eq_prod E E]
      exact (Measure.ae_prod_iff_ae_ae hz.measurableSet).2 (Filter.Eventually.of_forall fun _ => hq)
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards [axis] with p e
    simp only [radianTrilinearWeight, rem, radianFirstLowRemainder, if_neg e]
  obtain ⟨hSum,hSplit⟩ := hGapAssembly cutoff rem hRem.aestronglyMeasurable (B+B₀)
    (add_nonneg hB hB₀) hRemNorm hRemSupport f g h
  refine ⟨hSum, ?_⟩
  rw [radianTrilinearForm_first_low_split χ₀ hχ₀ hχ A gap hgap m M₀ hm hM₀ B B₀ hNorm hNorm₀ hB₀ f g h,
    hEqual, hSplit]

end Burnett.A05
