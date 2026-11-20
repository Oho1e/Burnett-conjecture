import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualBound
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualCutoffLp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Metric Filter
open CMBilinearDual
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

private def spectralPhase (x : E) (y : Joint) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * (inner ℝ y.1 x + inner ℝ y.2 x)) : ℂ) * Complex.I)

private def spectralDensity (m : Joint → ℝ) (F G : E → ℂ) (x : E) (y : Joint) : ℂ :=
  (m y : ℂ) * (spectralPhase x y * (F y.1 * G y.2))

/-- Actual bilinear frequency integral for potentially non-Schwartz inputs
specified by integrable spectra. -/
def jointSpectralBilinear (m : Joint → ℝ) (F G : E → ℂ) (x : E) : ℂ :=
  ∫ y, spectralDensity m F G x y

theorem jointSpectralBilinear_schwartz (m : Joint → ℝ) (f g : SchwartzMap E ℂ) :
    jointSpectralBilinear m (𝓕 (f : E → ℂ)) (𝓕 (g : E → ℂ)) = jointBilinear m f g := rfl

private theorem spectralDensity_integrable (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) {F G : E → ℂ} (hiF : Integrable F) (hiG : Integrable G) (x : E) :
    Integrable (spectralDensity m F G x) := by
  have b (y : Joint) : ‖spectralPhase x y‖ = 1 := by simp [spectralPhase, Complex.norm_exp]
  have c : Continuous (spectralPhase x) := by unfold spectralPhase; fun_prop
  have hi : Integrable (fun y : Joint => F y.1 * G y.2) := hiF.mul_prod hiG
  refine (hi.bdd_mul ((Complex.continuous_ofReal.measurable.comp hm).mul c.measurable).aestronglyMeasurable
    ⟨D, fun y => by simpa only [Function.comp_apply, norm_mul, b, mul_one, Complex.norm_real] using hD y⟩).congr ?_
  filter_upwards with y
  simp only [spectralDensity, mul_assoc, Function.comp_apply]

/-- Removing both input cutoffs recovers the actual bilinear frequency
integral at every physical point. -/
theorem jointSpectralBilinear_tendsto_annular (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (F G : E → ℂ)
    (fS : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (gS : ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0})
    (hiF : Integrable F) (hiG : Integrable G) (x : E) :
    Tendsto (fun n => jointBilinear m (annularInput F fS n) (annularInput G gS n) x)
      atTop (𝓝 (jointSpectralBilinear m F G x)) := by
  let A := spectralDensity m F G x
  let w := fun (n : ℕ) (y : Joint) => ((inputAnnularMask n y.1 : ℂ) * (inputAnnularMask n y.2 : ℂ))
  have hA : Integrable A := spectralDensity_integrable m hm hD hiF hiG x
  have cw (n : ℕ) : Continuous (w n) := by
    exact (Complex.continuous_ofReal.comp ((inputAnnularMask_contDiff n).continuous.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((inputAnnularMask_contDiff n).continuous.comp continuous_snd))
  have bw (n : ℕ) (y : Joint) : ‖w n y‖ ≤ 1 := by
    simp only [w, norm_mul, Complex.norm_real]
    exact mul_le_one₀ (inputAnnularMask_norm_le n y.1) (norm_nonneg _) (inputAnnularMask_norm_le n y.2)
  have h0 : ∀ᵐ ξ ∂(volume : Measure E), ξ ≠ 0 := (Set.countable_singleton (0 : E)).ae_notMem volume
  have h1 : ∀ᵐ y ∂(volume : Measure Joint), y.1 ≠ 0 := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.quasiMeasurePreserving_fst.ae h0
  have h2 : ∀ᵐ y ∂(volume : Measure Joint), y.2 ≠ 0 := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.quasiMeasurePreserving_snd.ae h0
  have lim : ∀ᵐ y ∂(volume : Measure Joint), Tendsto (fun n => w n y * A y) atTop (𝓝 (A y)) := by
    filter_upwards [h1, h2] with y hy hz
    apply tendsto_const_nhds.congr'
    filter_upwards [inputAnnularMask_eventually_one hy, inputAnnularMask_eventually_one hz] with n hn hn'
    simp only [w, hn, hn', Complex.ofReal_one, one_mul]
  have ht := tendsto_integral_of_dominated_convergence (F := fun n y => w n y * A y) (fun y => ‖A y‖)
    (fun n => (cw n).aestronglyMeasurable.mul hA.1) hA.norm
    (fun n => Eventually.of_forall fun y => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (bw n y)) lim
  refine ht.congr (fun n => ?_)
  apply integral_congr_ae
  filter_upwards with y
  unfold w A spectralDensity spectralPhase testCarrier
  rw [annularInput_fourier, annularInput_fourier]
  ring

private theorem annularInput_norm_tendsto (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0})
    (hiF : Integrable F) {p : ℝ} (hp : 1 < p) (hu : MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm (annularInput F hF n : E → ℂ) (ENNReal.ofReal p) volume) atTop
      (𝓝 (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume)) := by
  let P := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  let v := fun n => (annularInput F hF n).toLp P volume
  have conv : Tendsto v atTop (𝓝 (hu.toLp (𝓕⁻ F))) := by
    apply Lp.tendsto_Lp_of_tendsto_eLpNorm (𝓕⁻ F) hu
    have hn (n : ℕ) : eLpNorm ((v n : E → ℂ) - 𝓕⁻ F) P volume =
        eLpNorm ((annularInput F hF n : E → ℂ) - 𝓕⁻ F) P volume :=
      eLpNorm_congr_ae (((annularInput F hF n).coeFn_toLp P volume).sub EventuallyEq.rfl)
    exact (annularInput_tendsto_eLpNorm F hF hiF hp hu).congr (fun n => (hn n).symm)
  have vn (n : ℕ) : ‖v n‖ₑ = eLpNorm (annularInput F hF n : E → ℂ) P volume :=
    Lp.enorm_toLp ((annularInput F hF n).memLp P volume)
  simpa only [Function.comp_def, vn, Lp.enorm_toLp] using
    (continuous_enorm.tendsto (hu.toLp (𝓕⁻ F))).comp conv

/-- Transfer any proved Schwartz bilinear estimate to the actual frequency
integral with the same constant, for integrable spectra smooth off zero. -/
theorem joint_spectral_bilinear_of_schwartz_bound {p s r : ℝ} (hp : 1 < p) (hs : 1 < s)
    (m : Joint → ℝ) (hm : Measurable m) {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (bound : ∀ f g : SchwartzMap E ℂ,
      MemLp (jointBilinear m f g) (ENNReal.ofReal r) volume ∧
      eLpNorm (jointBilinear m f g) (ENNReal.ofReal r) volume ≤
        C * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume * eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume))
    (F G : E → ℂ) (fS : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (gS : ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0})
    (hiF : Integrable F) (hiG : Integrable G)
    (hpF : MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume) (hsG : MemLp (𝓕⁻ G) (ENNReal.ofReal s) volume) :
    MemLp (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ∧
      eLpNorm (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ≤
        C * (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) := by
  let f := annularInput F fS
  let g := annularInput G gS
  let u := fun n => jointBilinear m (f n) (g n)
  have meas (n : ℕ) : AEStronglyMeasurable (u n) volume := (bound (f n) (g n)).1.1
  have lim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun n => u n x) atTop (𝓝 (jointSpectralBilinear m F G x)) :=
    Eventually.of_forall (jointSpectralBilinear_tendsto_annular m hm hD F G fS gS hiF hiG)
  have nf := annularInput_norm_tendsto F fS hiF hp hpF
  have ng := annularInput_norm_tendsto G gS hiG hs hsG
  have conv := ENNReal.Tendsto.const_mul (a := C)
    (ENNReal.Tendsto.mul nf (Or.inr hsG.2.ne) ng (Or.inr hpF.2.ne)) (Or.inr hC.ne)
  have hbnd : eLpNorm (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ≤
      C * (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm meas _ lim).trans
      ((liminf_le_liminf (Eventually.of_forall fun n => (bound (f n) (g n)).2)).trans_eq conv.liminf_eq)
  exact ⟨⟨aestronglyMeasurable_of_tendsto_ae atTop meas lim,
    hbnd.trans_lt (ENNReal.mul_lt_top hC (ENNReal.mul_lt_top hpF.2 hsG.2))⟩, hbnd⟩

/-- The Coifman–Meyer estimate on the actual joint frequency integral, with
physical input norms when the integrable spectra need only be smooth off zero. -/
theorem joint_spectral_bilinear_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (F G : E → ℂ),
      ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0} → ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0} →
      Integrable F → Integrable G →
      MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume → MemLp (𝓕⁻ G) (ENNReal.ofReal s) volume →
      MemLp (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ∧
        eLpNorm (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ≤
          C * (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) := by
  obtain ⟨hm', _, hD⟩ := homogeneous_joint_symbol_measurable_bounded m hm hh
  obtain ⟨C, hC, bound⟩ := joint_bilinear_bound p s r hp hs hr he m hm hh
  exact ⟨C, hC, joint_spectral_bilinear_of_schwartz_bound hp hs m hm' hD hC bound⟩

/-- The same spectral-input estimate with explicit finite symbol dependence. -/
theorem joint_spectral_bilinear_sphere_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {y | y ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ 15 → ∀ ξ ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      ∀ (F G : E → ℂ), ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0} → ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0} →
        Integrable F → Integrable G →
        MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume → MemLp (𝓕⁻ G) (ENNReal.ofReal s) volume →
        MemLp (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ∧
          eLpNorm (jointSpectralBilinear m F G) (ENNReal.ofReal r) volume ≤
            K * ENNReal.ofReal D *
              (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) := by
  obtain ⟨K, hK, bound⟩ := joint_bilinear_sphere_bound p s r hp hs hr he
  refine ⟨K, hK, fun m hm hh D hD hj => ?_⟩
  obtain ⟨hm', _, hM⟩ := homogeneous_joint_symbol_measurable_bounded m hm hh
  exact joint_spectral_bilinear_of_schwartz_bound hp hs m hm' hM
    (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top) (bound m hm hh D hD hj)

end Burnett.A02.FrequencySplit
