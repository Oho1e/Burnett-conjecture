import Burnett.Analysis.Sobolev.Pairing
import Burnett.Analysis.Fourier.L2Extension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# LocalHminusFourier

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.LocalHminusFourier
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform RealInnerProductSpace
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing

/-- A fixed genuine cutoff supplies L1 integrability; the source itself need not be smooth. -/
theorem integrable_of_L2_cutoff {f : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) : Integrable f := by
  apply (integrable_value_product_of_memLp f hf χ).congr
  filter_upwards with x
  by_cases hx : f x = 0
  · simp [hx]
  · simp [hχ x hx]

theorem integral_norm_le_L2_cutoff {f : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) :
    (∫ x, ‖f x‖) ≤ ‖hf.toLp f‖ * ‖valueLp χ‖ := by
  have heq : (∫ x, ‖f x‖) = ∫ x, ‖f x‖ * (χ : Space → ℝ) x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : f x = 0
    · simp [hx]
    · simp [hχ x hx]
  have hinner : inner ℝ (hf.norm.toLp (fun x => ‖f x‖)) (valueLp χ) =
      ∫ x, ‖f x‖ * (χ : Space → ℝ) x := by
    rw [inner_valueLp]
    apply integral_congr_ae
    filter_upwards [hf.norm.coeFn_toLp] with x hx
    rw [hx]
  rw [heq, ← hinner]
  have hn : ‖hf.norm.toLp (fun x => ‖f x‖)‖ = ‖hf.toLp f‖ := by
    simp only [Lp.norm_toLp, eLpNorm_norm]
  rw [← hn]
  have hb : |inner ℝ (hf.norm.toLp (fun x => ‖f x‖)) (valueLp χ)| ≤
      ‖hf.norm.toLp (fun x => ‖f x‖)‖ * ‖valueLp χ‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ) (hf.norm.toLp (fun x => ‖f x‖)) (valueLp χ)
  exact (le_abs_self _).trans hb

theorem fourier_uniform_bound {f : ℕ → Space → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space)) (χ : D)
    (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B) (n : ℕ) (ξ : Space) :
    ‖𝓕 (fun x => (f n x : ℂ)) ξ‖ ≤ B * ‖valueLp χ‖ := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar (volume : Measure Space) (innerₗ Space) (fun x => (f n x : ℂ)) ξ
  have hb := integral_norm_le_L2_cutoff (hf n) χ (hχ n)
  have he : (∫ x, ‖(f n x : ℂ)‖) = ∫ x, ‖f n x‖ := by
    apply integral_congr_ae
    filter_upwards with x
    simp
  change ‖𝓕 (fun x => (f n x : ℂ)) ξ‖ ≤ _ at h
  rw [he] at h
  exact (h.trans hb).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))

def complexRealTest (ψ : Space → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) : D :=
  ⟨fun x => (ψ x).re, Complex.reCLM.contDiff.comp hψ, hcψ.comp_left (by simp)⟩

def complexImagTest (ψ : Space → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) : D :=
  ⟨fun x => (ψ x).im, Complex.imCLM.contDiff.comp hψ, hcψ.comp_left (by simp)⟩

theorem complex_test_tendsto_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    {ψ : Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, (f n x : ℂ) * ψ x) atTop (𝓝 0) := by
  have hr := (Complex.ofRealCLM.continuous.tendsto (0 : ℝ)).comp
    (ht (complexRealTest ψ hψ hcψ))
  have hi := (Complex.ofRealCLM.continuous.tendsto (0 : ℝ)).comp
    (ht (complexImagTest ψ hψ hcψ))
  have h := hr.add (hi.mul_const Complex.I)
  simp only [map_zero, zero_mul, zero_add] at h
  apply h.congr
  intro n
  have hint : Integrable (fun x => (f n x : ℂ) * ψ x) :=
    ((Complex.ofRealCLM.contDiff.comp (hs n)).mul hψ).continuous.integrable_of_hasCompactSupport
      hcψ.mul_left
  have heq := integral_re_add_im hint
  change (((∫ x, f n x * (ψ x).re) : ℝ) : ℂ) +
    ((∫ x, f n x * (ψ x).im) : ℝ) * Complex.I = _
  change (((∫ x, ((f n x : ℂ) * ψ x).re) : ℝ) : ℂ) +
    ((∫ x, ((f n x : ℂ) * ψ x).im) : ℝ) * Complex.I = _ at heq
  simpa only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using heq

def phase (ξ x : Space) : ℂ :=
  Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I)

theorem phase_smooth (ξ : Space) : ContDiff ℝ ∞ (phase ξ) := by
  have hi : ContDiff ℝ ∞ (fun x : Space => inner ℝ x ξ) := by
    simpa only [real_inner_comm] using (innerSL ℝ ξ).contDiff
  have ha : ContDiff ℝ ∞ (fun x : Space => -2 * Real.pi * inner ℝ x ξ) :=
    contDiff_const.mul hi
  have hb : ContDiff ℝ ∞ (fun x : Space =>
      ((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp ha).mul contDiff_const
  exact hb.cexp

theorem fourier_pointwise_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (χ : D)
    (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (ξ : Space) : Tendsto (fun n => 𝓕 (fun x => (f n x : ℂ)) ξ) atTop (𝓝 0) := by
  have hψ : ContDiff ℝ ∞ (fun x => ((χ : Space → ℝ) x : ℂ) * phase ξ x) :=
    (Complex.ofRealCLM.contDiff.comp (test_smooth χ)).mul (phase_smooth ξ)
  have hcψ : HasCompactSupport (fun x => ((χ : Space → ℝ) x : ℂ) * phase ξ x) :=
    ((test_compactSupport χ).comp_left Complex.ofReal_zero).mul_right
  have h := complex_test_tendsto_zero hs ht hψ hcψ
  apply h.congr
  intro n
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f n x = 0
  · simp [hx]
  · simp [hχ n x hx, phase, smul_eq_mul, mul_comm]

theorem source_hasCompactSupport {f : Space → ℝ} (χ : D)
    (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) : HasCompactSupport f := by
  have heq : f = fun x => (χ : Space → ℝ) x * f x := by
    funext x
    by_cases hx : f x = 0
    · simp [hx]
    · simp [hχ x hx]
  rw [heq]
  exact (test_compactSupport χ).mul_right

def sourceSchwartz {f : Space → ℝ} (hs : ContDiff ℝ ∞ f) (χ : D)
    (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) : SchwartzMap Space ℂ :=
  ((source_hasCompactSupport χ hχ).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hs)

theorem fourier_source_continuous {f : Space → ℝ} (hs : ContDiff ℝ ∞ f) (χ : D)
    (hχ : ∀ x, f x ≠ 0 → (χ : Space → ℝ) x = 1) :
    Continuous (𝓕 (fun x => (f x : ℂ))) :=
  (SchwartzMap.fourierTransformCLM ℂ (sourceSchwartz hs χ hχ)).continuous

theorem low_frequency_energy_tendsto_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (R : ℝ) :
    Tendsto (fun n => ∫ ξ in Metric.closedBall (0 : Space) R,
      ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2) atTop (𝓝 0) := by
  let S : Set Space := Metric.closedBall 0 R
  let C : ℝ := B * ‖valueLp χ‖
  have hC : 0 ≤ C := mul_nonneg ((norm_nonneg _).trans (hB 0)) (norm_nonneg _)
  letI : IsFiniteMeasure ((volume : Measure Space).restrict S) :=
    ⟨by simpa [S] using (isCompact_closedBall (0 : Space) R).measure_lt_top⟩
  have hm : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun ξ => ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2) (volume.restrict S) := by
    apply Eventually.of_forall
    intro n
    exact ((fourier_source_continuous (hs n) χ (hχ n)).norm.pow 2).aestronglyMeasurable
  have hb : ∀ᶠ n in atTop, ∀ᵐ ξ ∂volume.restrict S,
      ‖‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2‖ ≤ C^2 := by
    apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro ξ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (fourier_uniform_bound hf χ hχ hB n ξ)
  have hl : ∀ᵐ ξ ∂volume.restrict S, Tendsto
      (fun n => ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro ξ
    simpa using ((fourier_pointwise_zero hs χ hχ ht ξ).norm.pow 2)
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict S)
    (fun _ => C^2) hm hb (integrable_const _) hl
  simpa only [integral_zero] using h

end Burnett.Analysis.LocalHminusFourier
