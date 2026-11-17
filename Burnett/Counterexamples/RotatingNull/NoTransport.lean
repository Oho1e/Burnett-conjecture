import Burnett.Counterexamples.RotatingNull.MeasureModel
import Burnett.Counterexamples.RotatingNull.MeasureEstimates
import Burnett.Counterexamples.RotatingNull.SpacetimeCutoffs

noncomputable section
namespace Burnett.RotatingNullMoments.NoTransport
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators
open Burnett.RicciSymbol
open MeasureModel MeasureEstimates SpacetimeCutoffs ScaledCutoffs

theorem time_derivative_test (I : Set ℝ) (f : Burnett.CubicExplicit.Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    ContDiff ℝ ∞ (Burnett.CubicExplicit.D 0 f) ∧
      HasCompactSupport (Burnett.CubicExplicit.D 0 f) ∧
      tsupport (Burnett.CubicExplicit.D 0 f) ⊆ {x | x 0 ∈ I} := by
  have hs : tsupport (Burnett.CubicExplicit.D 0 f) ⊆ tsupport f := by
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hn
    apply hx
    simp [Burnett.CubicExplicit.D, fderiv_of_notMem_tsupport ℝ hn]
  refine ⟨?_, hc.fderiv_apply ℝ (Burnett.CubicExplicit.basis 0), hs.trans ht⟩
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem no_transported_positive_representation
    (I : Set ℝ) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I) (c : ℝ) (hc : 0 < c)
    (μ : Measure (UnitPhase I)) [IsLocallyFiniteMeasure μ]
    (hnull : IsNullSupported I μ) (hm : HasTensorMoments I c μ)
    (htransport : HasHamiltonTransport I μ) : False := by
  obtain ⟨χ, hχ, hcχ, htχ, hnχ, hiχ, hwχ⟩ := exists_time_cutoff I hI h0
  have htχI : tsupport χ ⊆ I := htχ.trans inter_subset_left
  obtain ⟨C, hC, hmajor⟩ := phi_spatial_majorant χ hχ hnχ
  let A : ℝ := 2*c * (∫ y : ScaledCutoffs.Space, spatialBump y) *
    (∫ t : ℝ, χ t * Real.cos (2*t))
  let B : ℝ := 2*c*C * (∫ y : ScaledCutoffs.Space, majorantBump y) * (∫ t : ℝ, χ t)
  have hA : 0 < A := by dsimp [A]; exact mul_pos (mul_pos (by positivity) spatialBump.integral_pos) hwχ
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (mul_pos (mul_pos (by positivity) hC) majorantBump.integral_pos) hiχ
  let R : ℝ := B/A + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let f := phi χ R
  let β := beta χ C R
  have hf : ContDiff ℝ ∞ f := phi_smooth χ hχ R
  have hcf : HasCompactSupport f := phi_compactSupport χ hcχ R hR
  have htf : tsupport f ⊆ {x | x 0 ∈ I} := phi_time_support χ I htχI R
  have hβ : ContDiff ℝ ∞ β := beta_smooth χ hχ C R
  have hcβ : HasCompactSupport β := beta_compactSupport χ hcχ C R hR
  have htβ : tsupport β ⊆ {x | x 0 ∈ I} := beta_time_support χ I htχI C R
  obtain ⟨hψ, hcψ, htψ⟩ := time_derivative_test I f hf hcf htf
  let ν := ambientMeasure I μ
  have ht : Integrable (temporalValue f) ν := by
    have h := ambient_component_integrable I hI μ (Burnett.CubicExplicit.D 0 f)
      hψ.continuous hcψ htψ 1 2
    convert h using 1
    funext p
    unfold temporalValue
    ring
  have hb : Integrable (weightedValue β) ν := by
    have h := ambient_moment00_integrable I hI μ β hβ.continuous hcβ htβ
    convert h using 1
    funext p
    unfold weightedValue
    ring
  have hz : (∫ p, hamiltonValue f p ∂ν) = 0 := by
    have h := ambient_transport I hI μ htransport (separatedTest f)
      (separatedTest_isTransportTest I f hf hcf htf)
    simpa only [CanonicalHamilton.canonicalHamilton_eq_flatHamilton, hamiltonValue] using h
  have ha := temporal_integral_bound_of_transport ν f β hf
    ((ambient_nonzero_ae I hI μ).and (ambient_null_ae I hI μ hnull)) (hmajor R hR) ht hb hz
  have htv : (∫ p, temporalValue f p ∂ν) = -(A*R^3) := by
    calc
      _ = ∫ p : MeasureModel.Phase, Burnett.CubicExplicit.D 0 f p.1 * p.2 1 * p.2 2 ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by unfold temporalValue; ring)
      _ = ∫ x : MeasureModel.Base, 2*c * (Real.cos (x 0) * Real.sin (x 0)) * Burnett.CubicExplicit.D 0 f x :=
        ambient_moment12 I hI c μ hm _ hψ hcψ htψ
      _ = 2*c * (∫ x : MeasureModel.Base, Burnett.CubicExplicit.D 0 f x * (Real.cos (x 0) * Real.sin (x 0))) := by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
      _ = _ := by rw [phi_temporal_integral χ hχ hcχ R hR]; dsimp [A]; ring
  have hbv : (∫ p, weightedValue β p ∂ν) = B*R^2 := by
    calc
      _ = ∫ p : MeasureModel.Phase, β p.1 * (p.2 0)^2 ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by unfold weightedValue; ring)
      _ = ∫ x : MeasureModel.Base, 2*c * β x := ambient_moment00 I hI c μ hm β hβ hcβ htβ
      _ = 2*c * (∫ x : MeasureModel.Base, β x) := integral_const_mul _ _
      _ = _ := by rw [beta_integral χ C R hR]; dsimp [B]; field_simp [hR.ne']
  rw [htv, hbv, abs_neg, abs_of_nonneg (mul_nonneg hA.le (pow_nonneg hR.le 3))] at ha
  have har : A*R ≤ B := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hR)).mp
    convert ha using 1; ring
  have heq : A*R = B+A := by dsimp [R]; field_simp [hA.ne']
  rw [heq] at har
  linarith

theorem no_exists_transported_positive_representation
    (I : Set ℝ) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I) (c : ℝ) (hc : 0 < c) :
    ¬ ∃ μ : Measure (UnitPhase I), IsLocallyFiniteMeasure μ ∧ IsNullSupported I μ ∧
      HasTensorMoments I c μ ∧ HasHamiltonTransport I μ := by
  rintro ⟨μ, hlf, hn, hm, ht⟩
  letI : IsLocallyFiniteMeasure μ := hlf
  exact no_transported_positive_representation I hI h0 c hc μ hn hm ht

/-- All asserted properties of the given rotating tensor and the obstruction
to a transported positive null-ray moment representation, on every open
time neighborhood of zero. Both time orientations are retained. -/
theorem rotating_null_moment_counterexample
    (I : Set ℝ) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I) (c : ℝ) (hc : 0 < c) :
    ContDiff ℝ ∞ (fun x : Burnett.CubicExplicit.Space => tensor c (x 0)) ∧
    (∀ t a b, tensor c t a b = tensor c t b a) ∧
    (∀ t (u : Covector), 0 ≤ ∑ a, ∑ b, tensor c t a b * u a * u b) ∧
    (∀ t, metricTrace NullScreen.minkowskiInverse (tensor c t) = 0) ∧
    (∀ x b, divergence c x b = 0) ∧
    (∀ t, symbolNorm NullScreen.minkowskiInverse (ray 1 t) = 0 ∧
      symbolNorm NullScreen.minkowskiInverse (ray (-1) t) = 0 ∧ ray 1 t ≠ 0 ∧ ray (-1) t ≠ 0) ∧
    (∀ t a b, tensor c t a b =
      c * (ray 1 t a * ray 1 t b + ray (-1) t a * ray (-1) t b)) ∧
    ¬ ∃ μ : Measure (UnitPhase I), IsLocallyFiniteMeasure μ ∧ IsNullSupported I μ ∧
      HasTensorMoments I c μ ∧ HasHamiltonTransport I μ := by
  refine ⟨tensor_spacetime_smooth c, tensor_symmetric c,
    (fun t u => tensor_positive_semidefinite c t hc.le u), tensor_trace_free c,
    tensor_divergence_free c, ?_, (fun _ _ _ => rfl),
    no_exists_transported_positive_representation I hI h0 c hc⟩
  intro t
  exact ⟨ray_null 1 t (by norm_num), ray_null (-1) t (by norm_num),
    ray_ne_zero 1 t, ray_ne_zero (-1) t⟩

end Burnett.RotatingNullMoments.NoTransport
