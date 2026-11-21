import Burnett.Analysis.CubicEnergy.BilinearMultiplier.FourierConvention
import Burnett.Analysis.CubicEnergy.JointMultiplier.PhysicalBandLimit

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace

/-- The actual pointwise bilinear multiplier with the shared Fourier phase. -/
def jointBilinear (m : Joint → ℝ) (f g : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ p, (m p : ℂ) * testCarrier f g x p

private def fourierAmplitude (m : Joint → ℝ) (f g : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  (m p : ℂ) * (𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2)

private theorem fourierAmplitude_measurable (m : Joint → ℝ) (hm : Measurable m)
    (f g : SchwartzMap E ℂ) : Measurable (fourierAmplitude m f g) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  exact (Complex.continuous_ofReal.measurable.comp hm).mul
    ((F.continuous.measurable.comp measurable_fst).mul (G.continuous.measurable.comp measurable_snd))

private theorem fourierAmplitude_integrable (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ p, ‖m p‖ ≤ D) (f g : SchwartzMap E ℂ) :
    Integrable (fourierAmplitude m f g) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  have h : Integrable (fun p : Joint => F p.1 * G p.2) := F.integrable.mul_prod G.integrable
  exact h.bdd_mul (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable
    ⟨D, fun p => by simpa only [Complex.norm_real] using hD p⟩

private def phase (x : E) (p : Joint) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * (inner ℝ p.1 x + inner ℝ p.2 x)) : ℂ) * Complex.I)

private theorem phase_norm (x : E) (p : Joint) : ‖phase x p‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem phase_continuous : Continuous (fun z : E × Joint => phase z.1 z.2) := by
  unfold phase
  fun_prop

private theorem phase_integral (h : SchwartzMap E ℂ) (p : Joint) :
    (∫ x, phase x p * h x) = 𝓕 (h : E → ℂ) (-(p.1 + p.2)) := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [phase, inner_neg_right, inner_add_right, real_inner_comm x p.1, real_inner_comm x p.2,
    smul_eq_mul, neg_mul, mul_neg, neg_neg]

private theorem jointBilinear_eq_integral (m : Joint → ℝ) (f g : SchwartzMap E ℂ) (x : E) :
    jointBilinear m f g x = ∫ p, fourierAmplitude m f g p * phase x p := by
  apply integral_congr_ae
  filter_upwards with p
  unfold fourierAmplitude testCarrier phase
  ring

/-- A bounded measurable joint symbol gives a continuous, bounded actual
output on Schwartz inputs. -/
theorem jointBilinear_continuous_bounded (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ p, ‖m p‖ ≤ D) (f g : SchwartzMap E ℂ) :
    Continuous (jointBilinear m f g) ∧ ∃ B : ℝ, ∀ x, ‖jointBilinear m f g x‖ ≤ B := by
  let A := fourierAmplitude m f g
  have hi : Integrable A := fourierAmplitude_integrable m hm hD f g
  have norm_amp (x : E) (p : Joint) : ‖A p * phase x p‖ = ‖A p‖ := by
    rw [norm_mul, phase_norm, mul_one]
  constructor
  · have eq : jointBilinear m f g = fun x => ∫ p, A p * phase x p :=
      funext (jointBilinear_eq_integral m f g)
    rw [eq]
    apply continuous_of_dominated (bound := fun p => ‖A p‖) ?_ ?_ hi.norm ?_
    · intro x
      have hc : Continuous (phase x) := by unfold phase; fun_prop
      exact hi.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun p => (norm_amp x p).le
    · exact Filter.Eventually.of_forall fun p => continuous_const.mul (by unfold phase; fun_prop)
  · refine ⟨∫ p, ‖A p‖, fun x => ?_⟩
    rw [jointBilinear_eq_integral]
    exact (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (Filter.Eventually.of_forall (norm_amp x)))

/-- The whole-space bilinear pairing in physical space equals its absolutely
integrable frequency pairing at the negative output frequency. -/
theorem jointBilinear_schwartz_pairing (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ p, ‖m p‖ ≤ D) (f g h : SchwartzMap E ℂ) :
    Integrable (fun x => jointBilinear m f g x * h x) ∧
      Integrable (bilinearFourierWeight m f g h) ∧
      (∫ x, jointBilinear m f g x * h x) = ∫ p, bilinearFourierWeight m f g h p := by
  let A := fourierAmplitude m f g
  let H := SchwartzMap.fourierTransformCLM ℂ h
  have hi : Integrable A := fourierAmplitude_integrable m hm hD f g
  obtain ⟨hc, hb⟩ := jointBilinear_continuous_bounded m hm hD f g
  refine ⟨h.integrable.bdd_mul hc.aestronglyMeasurable hb, ?_, ?_⟩
  · have hH : Continuous (fun p : Joint => H (-(p.1 + p.2))) :=
      H.continuous.comp (continuous_fst.add continuous_snd).neg
    have bi := hi.bdd_mul hH.aestronglyMeasurable ⟨_, fun p => H.norm_le_seminorm ℂ (-(p.1 + p.2))⟩
    refine bi.congr <| Filter.Eventually.of_forall fun p => ?_
    change 𝓕 (h : E → ℂ) (-(p.1 + p.2)) * fourierAmplitude m f g p =
      bilinearFourierWeight m f g h p
    unfold fourierAmplitude bilinearFourierWeight
    ring
  let T := fun (x : E) (p : Joint) => A p * (phase x p * h x)
  have hT : Integrable (Function.uncurry T) ((volume : Measure E).prod volume) := by
    have mm : Measurable (Function.uncurry T) :=
      ((fourierAmplitude_measurable m hm f g).comp measurable_snd).mul
        (phase_continuous.measurable.mul (h.continuous.measurable.comp measurable_fst))
    refine (h.integrable.norm.mul_prod hi.norm).mono' mm.aestronglyMeasurable ?_
    filter_upwards with z
    change ‖A z.2 * (phase z.1 z.2 * h z.1)‖ ≤ ‖h z.1‖ * ‖A z.2‖
    simp only [norm_mul, phase_norm, one_mul, mul_comm, le_refl]
  have left (x : E) : jointBilinear m f g x * h x = ∫ p, T x p := by
    rw [jointBilinear_eq_integral, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with p
    exact mul_assoc _ _ _
  simp_rw [left]
  rw [integral_integral_swap hT]
  apply integral_congr_ae
  filter_upwards with p
  change (∫ x, A p * (phase x p * h x)) = _
  rw [integral_const_mul, phase_integral]
  change fourierAmplitude m f g p * 𝓕 (h : E → ℂ) (-(p.1 + p.2)) = bilinearFourierWeight m f g h p
  unfold fourierAmplitude bilinearFourierWeight
  ring

/-- The symbol hypotheses used in the joint dyadic reconstruction give
measurability and a global bound, including the assigned value at zero. -/
theorem homogeneous_joint_symbol_measurable_bounded (m : Joint → ℝ)
    (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0}) (hh : ∀ t : ℝ, 0 < t → ∀ p, m (t • p) = m p) :
    Measurable m ∧ ∃ D : ℝ, ∀ p, ‖m p‖ ≤ D := by
  refine ⟨measurable_of_continuousOn_compl_singleton 0 hs.continuousOn, ?_⟩
  obtain ⟨D, _, bound⟩ := degreeZero_derivative_bounds m hs hh 0
  refine ⟨max D ‖m 0‖, fun p => ?_⟩
  by_cases hp : p = 0
  · simpa only [hp] using le_max_right D ‖m 0‖
  · exact (by simpa using bound p hp : ‖m p‖ ≤ D).trans (le_max_left _ _)

end Burnett.A02.FrequencySplit
