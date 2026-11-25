import Burnett.Analysis.AllScaleTransfer.ActualCapAxialWindows

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.A05

open Set MeasureTheory Filter
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps

/-- The same axial window in all three slots of the comparable coefficient. -/
def axialComparableWindow (α : ℝ) (p : Joint) : ℝ :=
  axialCapPairWindow α p * axialCapWindow α (-(p.1+p.2))

def axialComparableSymbol (α : ℝ) (m : Joint → ℂ) (p : Joint) : ℂ :=
  (axialComparableWindow α p : ℂ) * m p

theorem axialComparableSymbol_aestronglyMeasurable (α : ℝ) {m : Joint → ℂ}
    (hm : AEStronglyMeasurable m volume) :
    AEStronglyMeasurable (axialComparableSymbol α m) volume := by
  have h : Measurable (axialComparableWindow α) :=
    (((axialCapWindow_measurable α).comp measurable_fst).mul
      ((axialCapWindow_measurable α).comp measurable_snd)).mul
      ((axialCapWindow_measurable α).comp (measurable_fst.add measurable_snd).neg)
  exact (Complex.continuous_ofReal.measurable.comp h).aestronglyMeasurable.mul hm

theorem axialComparableSymbol_pos_smul (α : ℝ) {m : Joint → ℂ}
    (hm : ∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p)
    (t : ℝ) (ht : 0 < t) (p : Joint) :
    axialComparableSymbol α m (t • p) = axialComparableSymbol α m p := by
  unfold axialComparableSymbol axialComparableWindow axialCapPairWindow
  rw [hm _ ht]
  have e : -(t • p.1+t • p.2) = t • (-(p.1+p.2)) := by rw [smul_neg,smul_add]
  change (↑(axialCapWindow α (t • p.1) * axialCapWindow α (t • p.2) *
    axialCapWindow α (-(t • p.1+t • p.2))) : ℂ) * m p = _
  rw [e, axialCapWindow_pos_smul α t ht p.1, axialCapWindow_pos_smul α t ht p.2,
    axialCapWindow_pos_smul α t ht (-(p.1+p.2))]

private theorem triad_frequencies_ne_zero_ae :
    ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ -(p.1+p.2) ≠ 0 := by
  have h (x : E) : ∀ᵐ y ∂(volume : Measure E), y ≠ x := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton x).ae_notMem (volume : Measure E)
  have o₁ : IsOpen {p : Joint | p.1 ≠ (0 : E)} := isOpen_ne_fun continuous_fst continuous_const
  have o₂ : IsOpen {p : Joint | p.2 ≠ (0 : E)} := isOpen_ne_fun continuous_snd continuous_const
  have o₃ : IsOpen {p : Joint | -(p.1+p.2) ≠ (0 : E)} :=
    isOpen_ne_fun (continuous_fst.add continuous_snd).neg continuous_const
  rw [Measure.volume_eq_prod E E]
  apply (Measure.ae_prod_iff_ae_ae (o₁.inter (o₂.inter o₃)).measurableSet).2
  filter_upwards [h 0] with x hx
  filter_upwards [h 0,h (-x)] with y hy hyx
  refine ⟨hx,hy,?_⟩
  intro hz
  have hxy : x+y = 0 := neg_eq_zero.mp hz
  exact hyx (by calc
    y = x+y-x := by abel
    _ = -x := by rw [hxy,zero_sub])

/-- The three actual closed enlarged cap supports give a plateau off the
null frequency axes. Where the new coefficient is nonzero, all three
frequencies admit the same lower norm comparison for the same cap map. -/
theorem exists_actual_cap_comparable_axial_localization (B tube outer enlarged : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ α L U : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < L ∧ 0 < U ∧
      ∀ (metric : Form) (u : Vec) (F : NullCapChart metric u),
        ‖u‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
          let A := capFrequencyEquiv F hδ.ne'
          let P := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged u)
          (∀ p : Joint, axialComparableWindow α p ≠ 0 →
            let w := -(p.1+p.2)
            (L*‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖ ≤ U*‖p.1‖) ∧
            (L*‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.2‖ ≤ U*‖p.2‖) ∧
            (L*‖w‖ ≤ ‖A w‖ ∧ ‖A w‖ ≤ U*‖w‖)) ∧
          ∀ (f g h : SchwartzMap E ℂ),
            (∀ p : Joint, radianWeight (fun _ => 1) f g h p ≠ 0 →
              A p.1 ∈ P ∧ A p.2 ∈ P ∧ A (-(p.1+p.2)) ∈ P) →
            ∀ m : Joint → ℂ, radianTrilinearForm (axialComparableSymbol α m) f g h =
              radianTrilinearForm m f g h := by
  obtain ⟨α,L,hα,hα₁,hL,hLdef,hAx⟩ :=
    exists_actual_cap_axial_window_localization B tube outer enlarged hB hTube hOut hOE
  let U := B * ‖frequencyCoordinates.toContinuousLinearMap‖+1
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨α,L,U,hα,hα₁,hL,hU,?_⟩
  intro metric u F hu hF hFI δ hδ hδ₁ hsmall A P
  obtain ⟨plateau,_,_⟩ := hAx metric u F hu hFI δ hδ hsmall
  have lower (x : E) (hx : axialCapWindow α x ≠ 0) : L*‖x‖ ≤ ‖A x‖ := by
    rw [hLdef]
    apply capFrequencyEquiv_lower_on_axial_cone F hδ.ne' hB hFI
    rw [BoxFourier.frequencyCoordinates_axis]
    exact (axialCapWindow_nonzero_cone hα hx).2.le
  have upper (x : E) : ‖A x‖ ≤ U*‖x‖ := by
    have hOp := capFrequencyEquiv_opNorm_le F hδ hδ₁ hB.le hF
    exact (A.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hOp.trans (by dsimp [U]; linarith)) (norm_nonneg _))
  refine ⟨?_,?_⟩
  · intro p hp w
    have hW : axialCapWindow α w ≠ 0 := right_ne_zero_of_mul hp
    have hPair : axialCapPairWindow α p ≠ 0 := left_ne_zero_of_mul hp
    exact ⟨⟨lower p.1 (left_ne_zero_of_mul hPair),upper p.1⟩,
      ⟨lower p.2 (right_ne_zero_of_mul hPair),upper p.2⟩,⟨lower w hW,upper w⟩⟩
  · intro f g h hSupport m
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards [triad_frequencies_ne_zero_ae] with p ⟨hp,hq,hr⟩
    by_cases hW : radianWeight (fun _ => 1) f g h p = 0
    · simp only [radianTrilinearWeight,hW,mul_zero]
    obtain ⟨cp,cq,cr⟩ := hSupport p hW
    simp only [radianTrilinearWeight,axialComparableSymbol,axialComparableWindow,
      axialCapPairWindow,plateau _ hp cp,plateau _ hq cq,plateau _ hr cr,mul_one,Complex.ofReal_one,one_mul]

end Burnett.A05
