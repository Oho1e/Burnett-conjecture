import Burnett.Analysis.AllScaleTransfer.ActualCapAxial
import Burnett.Analysis.AllScaleTransfer.ActualCapRadialSeminorm
import Burnett.Analysis.AllScaleTransfer.EndpointAngularModeJets
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A05

open Set Filter MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier (frequencyCoordinates_axis)
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

/-- The signs of the axial coordinate give the same cutoff. -/
def axialCapWindow (α : ℝ) (p : E) : ℝ :=
  descendingProfile (-(α^2)) (-((α/2)^2)) (-((endpointDirection p 0)^2))

def axialCapPairWindow (α : ℝ) (p : Joint) : ℝ := axialCapWindow α p.1 * axialCapWindow α p.2

private theorem axialThresholds {α : ℝ} (hα : 0 < α) : -(α^2) < -((α/2)^2) := by
  nlinarith only [sq_pos_of_pos hα]

private theorem unitAxis_abs (p : E) :
    |endpointDirection p 0| = |p 0| / ‖p‖ := by
  change |‖p‖⁻¹ * p 0| = _
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_eq_div]

theorem axialCapWindow_contDiffOn (α : ℝ) : ContDiffOn ℝ ∞ (axialCapWindow α) {p : E | p ≠ 0} := by
  have axis : ContDiff ℝ ∞ (fun p : E => p 0) := frequencyCoordinates.toContinuousLinearMap.contDiff.fst
  have u : ContDiffOn ℝ ∞ (fun p : E => endpointDirection p 0) {p : E | p ≠ 0} :=
    axis.comp_contDiffOn endpointDirection_contDiffOn
  exact (descendingProfile_contDiff _ _).comp_contDiffOn ((u.pow 2).neg)

theorem axialCapWindow_measurable (α : ℝ) : Measurable (axialCapWindow α) := by
  have normdir : Measurable endpointDirection := by unfold endpointDirection; fun_prop
  have axis : Continuous (fun p : E => p 0) := frequencyCoordinates.continuous.fst
  exact (descendingProfile_contDiff _ _).continuous.measurable.comp ((axis.measurable.comp normdir).pow_const 2).neg

theorem axialCapWindow_pos_smul (α : ℝ) (t : ℝ) (ht : 0 < t) (p : E) :
    axialCapWindow α (t • p) = axialCapWindow α p := by
  simp only [axialCapWindow,endpointDirection_pos_smul t ht]

theorem axialCapWindow_direction (α : ℝ) (p : E) :
    axialCapWindow α (endpointDirection p) = axialCapWindow α p := by
  by_cases hp : p = 0
  · simp only [hp,endpointDirection,norm_zero,inv_zero,zero_smul]
  · exact axialCapWindow_pos_smul α ‖p‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hp)) p

theorem axialCapWindow_range (α : ℝ) (p : E) : 0 ≤ axialCapWindow α p ∧ axialCapWindow α p ≤ 1 :=
  descendingProfile_range _ _ _

theorem axialCapWindow_eq_one {α : ℝ} (hα : 0 < α) {p : E} (hp : p ≠ 0)
    (h : α * ‖p‖ ≤ |p 0|) : axialCapWindow α p = 1 := by
  have ha : α ≤ |endpointDirection p 0| := by
    rw [unitAxis_abs p]
    exact (le_div_iff₀ (norm_pos_iff.mpr hp)).mpr h
  have hsq := (sq_le_sq₀ hα.le (abs_nonneg _)).mpr ha
  rw [sq_abs] at hsq
  exact descendingProfile_eq_one (axialThresholds hα) (neg_le_neg hsq)

theorem axialCapWindow_eq_zero {α : ℝ} (hα : 0 < α) {p : E}
    (h : |p 0| ≤ (α/2) * ‖p‖) : axialCapWindow α p = 0 := by
  have ha : |endpointDirection p 0| ≤ α/2 := by
    by_cases hp : p = 0
    · simpa only [hp,endpointDirection,norm_zero,inv_zero,zero_smul,PiLp.zero_apply,abs_zero]
        using (half_pos hα).le
    · rw [unitAxis_abs p]
      exact (div_le_iff₀ (norm_pos_iff.mpr hp)).mpr h
  have hsq := (sq_le_sq₀ (abs_nonneg _) (half_pos hα).le).mpr ha
  rw [sq_abs] at hsq
  exact descendingProfile_eq_zero (axialThresholds hα) (neg_le_neg hsq)

theorem axialCapWindow_nonzero_cone {α : ℝ} (hα : 0 < α) {p : E}
    (h : axialCapWindow α p ≠ 0) : p ≠ 0 ∧ (α/2) * ‖p‖ < |p 0| := by
  have hs : (α/2) * ‖p‖ < |p 0| := lt_of_not_ge (fun hc => h (axialCapWindow_eq_zero hα hc))
  refine ⟨?_,hs⟩
  intro hp
  subst p
  simp at hs

def axialLocalizeRatio (α : ℝ) (M : Joint → ℝ → ℂ) (x : Joint) (ρ : ℝ) : ℂ :=
  (axialCapPairWindow α x : ℂ) * M x ρ

def axialLocalizeEndpoint (α : ℝ) (M₀ : Joint → ℂ) (x : Joint) : ℂ :=
  (axialCapPairWindow α x : ℂ) * M₀ x

/-- The localized ratio profile has the localized trace of that same symbol. -/
theorem axialLocalizeRatio_trace (α : ℝ) (M : Joint → ℝ → ℂ) (x : Joint) :
    axialLocalizeRatio α M x 0 = axialLocalizeEndpoint α (fun y => M y 0) x := rfl

theorem axialLocalizeRatio_eval (α : ℝ) (M : Joint → ℝ → ℂ) (p : Joint) (ρ : ℝ) :
    axialLocalizeRatio α M (endpointDirection p.1,endpointDirection p.2) ρ =
      (axialCapPairWindow α p : ℂ) * M (endpointDirection p.1,endpointDirection p.2) ρ := by
  rw [axialLocalizeRatio]
  congr 2
  simp only [axialCapPairWindow,axialCapWindow_direction]

theorem axialLocalizeEndpoint_measurable_bounded (α : ℝ) (M₀ : Joint → ℂ)
    (hM : Measurable M₀) (B : ℝ) (hBound : ∀ p, ‖M₀ p‖ ≤ B) :
    Measurable (axialLocalizeEndpoint α M₀) ∧ ∀ p, ‖axialLocalizeEndpoint α M₀ p‖ ≤ B := by
  have meas : Measurable (axialCapPairWindow α) :=
    ((axialCapWindow_measurable α).comp measurable_fst).mul ((axialCapWindow_measurable α).comp measurable_snd)
  refine ⟨(Complex.continuous_ofReal.measurable.comp meas).mul hM,?_⟩
  intro p
  have hp := axialCapWindow_range α p.1
  have hq := axialCapWindow_range α p.2
  have pair : 0 ≤ axialCapPairWindow α p ∧ axialCapPairWindow α p ≤ 1 :=
    ⟨mul_nonneg hp.1 hq.1,mul_le_one₀ hp.2 hq.1 hq.2⟩
  rw [axialLocalizeEndpoint,norm_mul,Complex.norm_real,Real.norm_of_nonneg pair.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) pair.2).trans (hBound p)

theorem axialLocalizeEndpoint_eval (α : ℝ) (M₀ : Joint → ℂ) (p : Joint) :
    axialLocalizeEndpoint α M₀ (endpointDirection p.1,endpointDirection p.2) =
      (axialCapPairWindow α p : ℂ) * M₀ (endpointDirection p.1,endpointDirection p.2) := by
  exact axialLocalizeRatio_eval α (fun x _ => M₀ x) p 0

private theorem axial_frequency_pair_ne_zero_ae :
    ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  let μ : Measure E := volume
  have h : ∀ᵐ x : E ∂μ, x ≠ 0 := (Set.countable_singleton (0 : E)).ae_notMem μ
  rw [Measure.volume_eq_prod E E]
  exact Filter.Eventually.and ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h)
    ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h)

/-- The same fixed axial window is one on the actual nonzero cap support.
On its nonzero set the true parabolic map has a common positive lower
constant in both slots. The Fourier identity is pointwise off the axes,
also at any point where the original three input factors vanish. -/
theorem exists_actual_cap_axial_window_localization (B tube outer enlarged : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ α L : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < L ∧ L = (α/2)/B ∧
      ∀ (m : Form) (u : Vec) (F : NullCapChart m u),
        ‖u‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4*B*(5*δ) ≤ 1 →
          let A := capFrequencyEquiv F hδ.ne'
          let P := tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged u)
          (∀ p : E, p ≠ 0 → A p ∈ P → axialCapWindow α p = 1) ∧
          (∀ p : Joint, axialCapPairWindow α p ≠ 0 →
            p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ L * ‖p.1‖ ≤ ‖A p.1‖ ∧ L * ‖p.2‖ ≤ ‖A p.2‖) ∧
          ∀ (f g h : SchwartzMap E ℂ),
            (∀ p, radianFourier f p ≠ 0 → A p ∈ P) →
            (∀ q, radianFourier g q ≠ 0 → A q ∈ P) →
            ∀ s : Joint → ℂ,
              let localized (p : Joint) := (axialCapPairWindow α p : ℂ) * s p
              (∀ p : Joint, (p.1 ≠ 0 ∧ p.2 ≠ 0) ∨ radianWeight (fun _ => 1) f g h p = 0 →
                radianTrilinearWeight localized f g h p = radianTrilinearWeight s f g h p) ∧
              radianTrilinearForm localized f g h = radianTrilinearForm s f g h := by
  obtain ⟨α,hα,hα1,axis⟩ := Burnett.A05.BoxFourier.exists_enlarged_cap_support_axial_margin B tube outer enlarged
    hB hTube hOut hOE
  let L := (α/2)/B
  refine ⟨α,L,hα,hα1,div_pos (half_pos hα) hB,rfl,?_⟩
  intro m u F hu hI δ hδ hSmall A P
  have plateau (p : E) (hp : p ≠ 0) (hP : A p ∈ P) : axialCapWindow α p = 1 :=
    axialCapWindow_eq_one hα hp (axis m u F hu hI δ hδ hSmall p hP)
  have lower (p : E) (hp : axialCapWindow α p ≠ 0) : p ≠ 0 ∧ L * ‖p‖ ≤ ‖A p‖ := by
    obtain ⟨hne,haxis⟩ := axialCapWindow_nonzero_cone hα hp
    refine ⟨hne,capFrequencyEquiv_lower_on_axial_cone F hδ.ne' hB hI ?_⟩
    rw [frequencyCoordinates_axis]
    exact haxis.le
  refine ⟨plateau,?_,?_⟩
  · intro p hp
    have h₁ := lower p.1 (left_ne_zero_of_mul hp)
    have h₂ := lower p.2 (right_ne_zero_of_mul hp)
    exact ⟨h₁.1,h₂.1,h₁.2,h₂.2⟩
  intro f g h hf hg s localized
  have point (p : Joint) (hp : (p.1 ≠ 0 ∧ p.2 ≠ 0) ∨ radianWeight (fun _ => 1) f g h p = 0) :
      radianTrilinearWeight localized f g h p = radianTrilinearWeight s f g h p := by
    rcases hp with hp | hp
    · by_cases h₁ : radianFourier f p.1 = 0
      · simp only [radianTrilinearWeight,radianWeight,h₁,mul_zero,zero_mul]
      by_cases h₂ : radianFourier g p.2 = 0
      · simp only [radianTrilinearWeight,radianWeight,h₂,mul_zero,zero_mul]
      simp only [radianTrilinearWeight,localized,axialCapPairWindow,plateau p.1 hp.1 (hf p.1 h₁),
        plateau p.2 hp.2 (hg p.2 h₂),mul_one,Complex.ofReal_one,one_mul]
    · simp only [radianTrilinearWeight,hp,mul_zero]
  refine ⟨point,?_⟩
  unfold radianTrilinearForm
  congr 1
  apply integral_congr_ae
  filter_upwards [axial_frequency_pair_ne_zero_ae] with p hp
  exact point p (Or.inl hp)

end Burnett.A05
