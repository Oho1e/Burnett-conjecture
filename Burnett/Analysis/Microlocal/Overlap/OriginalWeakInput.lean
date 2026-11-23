import Burnett.Analysis.Microlocal.OriginalVolumePairingLimits
import Burnett.Analysis.Fourier.SchwartzDensity
import Burnett.Geometry.AuxiliaryAdmissibility

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.OriginalCoordinateCurl
open Burnett.F05.CoordinateCurl (exists_outerCutoff_on_tsupport)
open Burnett.X02.SobolevTestJet (D Space test_smooth test_compactSupport)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

/-- Distributional vanishing on real compact tests gives weak complex L²
convergence for the actual real-valued Schwartz representatives. -/
theorem sourceSchwartz_weakL2_zero
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ n, ‖(sourceSchwartz (hs n) χ (hχ n)).toLp 2 volume‖ ≤ B)
    (ht : ∀ ψ : D, Tendsto (fun n => ∫ x, f n x * (ψ : Space → ℝ) x) atTop (𝓝 0)) :
    ∀ w : ComplexL2 Space, Tendsto (fun n =>
      inner ℂ w ((sourceSchwartz (hs n) χ (hχ n)).toLp 2 volume)) atTop (𝓝 0) := by
  let U (n : ℕ) := (sourceSchwartz (hs n) χ (hχ n)).toLp 2 volume
  have hSch (v : SchwartzMap Space ℂ) :
      Tendsto (fun n => inner ℂ (v.toLp 2 volume) (U n)) atTop (𝓝 0) := by
    let ψR : D := ⟨fun x => (χ : Space → ℝ) x * (v x).re,
      (test_smooth χ).mul (Complex.reCLM.contDiff.comp (v.smooth (⊤ : ℕ∞))),
      (test_compactSupport χ).mul_right⟩
    let ψI : D := ⟨fun x => (χ : Space → ℝ) x * (v x).im,
      (test_smooth χ).mul (Complex.imCLM.contDiff.comp (v.smooth (⊤ : ℕ∞))),
      (test_compactSupport χ).mul_right⟩
    let T := v.toLp 2 volume
    have hPairR (n : ℕ) : (inner ℂ T (U n)).re = ∫ x, f n x * (ψR : Space → ℝ) x := by
      rw [L2.inner_def]
      change RCLike.re (∫ x, inner ℂ (T x) (U n x)) = _
      rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) T (U n))]
      apply integral_congr_ae
      filter_upwards [v.coeFn_toLp 2 volume, (sourceSchwartz (hs n) χ (hχ n)).coeFn_toLp 2 volume] with x hx hy
      change T x = v x at hx
      change U n x = (f n x : ℂ) at hy
      rw [hx, hy]
      change (inner ℂ (v x) (f n x : ℂ)).re = f n x * ((χ : Space → ℝ) x * (v x).re)
      by_cases h : f n x = 0
      · simp [h]
      · simp [Complex.mul_re, hχ n x h]
    have hPairI (n : ℕ) : (inner ℂ T (U n)).im = -(∫ x, f n x * (ψI : Space → ℝ) x) := by
      rw [L2.inner_def]
      change RCLike.im (∫ x, inner ℂ (T x) (U n x)) = _
      rw [← integral_im (L2.integrable_inner (𝕜 := ℂ) T (U n)), ← integral_neg]
      apply integral_congr_ae
      filter_upwards [v.coeFn_toLp 2 volume, (sourceSchwartz (hs n) χ (hχ n)).coeFn_toLp 2 volume] with x hx hy
      change T x = v x at hx
      change U n x = (f n x : ℂ) at hy
      rw [hx, hy]
      change (inner ℂ (v x) (f n x : ℂ)).im = -(f n x * ((χ : Space → ℝ) x * (v x).im))
      by_cases h : f n x = 0
      · simp [h]
      · simp [Complex.mul_im, hχ n x h]
    have hR : Tendsto (fun n => (inner ℂ T (U n)).re) atTop (𝓝 0) := by
      simpa only [hPairR] using ht ψR
    have hI : Tendsto (fun n => (inner ℂ T (U n)).im) atTop (𝓝 0) := by
      simpa only [hPairI, neg_zero] using (ht ψI).neg
    have hR' := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hR
    have hI' := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hI
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, zero_add, Complex.re_add_im] using
      hR'.add (hI'.mul_const Complex.I)
  intro w
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨v, hv⟩ := Metric.denseRange_iff.mp schwartz_toLp_denseRange w δ hδ
  let T := v.toLp 2 volume
  have hT : ‖w - T‖ < δ := by simpa only [T, dist_eq_norm] using hv
  have hδB : δ * B ≤ ε / 2 := by
    have hEq : δ * (2 * (B + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ.le]
  have hEventually := (Metric.tendsto_nhds.mp (hSch v)) (ε / 2) (by positivity)
  filter_upwards [hEventually] with n hSmall
  rw [dist_zero_right] at hSmall ⊢
  have hErr : ‖inner ℂ (w - T) (U n)‖ ≤ ε / 2 :=
    (norm_inner_le_norm _ _).trans ((mul_le_mul hT.le (hN n) (norm_nonneg _) hδ.le).trans hδB)
  rw [show w = (w - T) + T by abel, inner_add_left]
  exact (norm_add_le _ _).trans_lt (by linarith : _ < ε)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The original volume-weighted coordinate gradient has bounded weakly
null representatives suitable for the overlap kernel estimates. -/
theorem exists_originalVolume_weakL2_representatives
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) :
    ∃ f : ℕ → JetSlot → SchwartzMap Space ℂ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ n i, (f n i).toLp 2 volume = originalGradient_volumeWeightedL2 B g hB hg hnB
        q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart) n i) ∧
      (∀ n i, tsupport (f n i : Space → ℂ) ⊆ q.ball.closedBall) ∧
      (∀ n i, ‖(f n i).toLp 2 volume‖ ≤ C) ∧
      ∀ i (w : ComplexL2 Space),
        Tendsto (fun n => inner ℂ w ((f n i).toLp 2 volume)) atTop (𝓝 0) := by
  let v := volumeModeInput B hB hnB q
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport v.cutoff
  obtain ⟨f, hs, hf, η, hη, C, hC, hBound, hWeak, _, hSupp, hSch, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r B g hB hg hnB hconv hb v.center v.cutoff
      (v.cutoff_support.trans v.ball_in_chart) θ hθ
  let F (n : ℕ) (i : JetSlot) := sourceSchwartz (hs n i) η (hη n i)
  have hNorm (n : ℕ) (i : JetSlot) : ‖(F n i).toLp 2 volume‖ ≤ C := by
    refine (Lp.norm_le_norm_of_ae_le (g := (hf n i).toLp (f n i)) ?_).trans (hBound n i)
    filter_upwards [(F n i).coeFn_toLp 2 volume, (hf n i).coeFn_toLp] with x hx hy
    rw [hx, hy]
    change ‖(f n i x : ℂ)‖ ≤ ‖f n i x‖
    simp
  have hFSupp (n : ℕ) (i : JetSlot) : tsupport (F n i : Space → ℂ) ⊆ q.ball.closedBall := by
    apply (closure_mono ?_).trans ((hSupp n i).trans v.cutoff_support)
    intro x hx
    change (f n i x : ℂ) ≠ 0 at hx
    exact fun h => hx (by simp [h])
  refine ⟨F, C, hC, fun n i => ?_, hFSupp, hNorm, fun i => ?_⟩
  · exact congrArg (fun p : SchwartzMap Space ℂ => p.toLp 2 volume) (congrFun (hSch n) i)
  · exact sourceSchwartz_weakL2_zero (fun n => f n i) (fun n => hs n i) η
      (fun n => hη n i) C hC (fun n => hNorm n i) (hWeak i)

end Burnett.Microlocal.Overlap
