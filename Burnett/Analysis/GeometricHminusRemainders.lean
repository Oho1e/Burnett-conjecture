import Burnett.Analysis.LocalWeakRicci
import Burnett.Analysis.StrongL2Hminus

set_option autoImplicit false

noncomputable section
set_option synthInstance.maxHeartbeats 200000

namespace Burnett.Analysis.GeometricHminusRemainders

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open LocalWeakDerivative

theorem localized_contDiff {U : Set CoordinateSpace} (hU : IsOpen U)
    {χ f : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun y => χ y * f y) :=
  contDiff_test_mul_local hU hχ hsχ hf

theorem localized_memLp {U : Set CoordinateSpace} (hU : IsOpen U)
    {χ f : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    MemLp (fun y => χ y * f y) 2 (volume : Measure CoordinateSpace) :=
  (localized_contDiff hU hχ hsχ hf).continuous.memLp_of_hasCompactSupport hcχ.mul_right

theorem localized_toLp_tendsto_zero {U : Set CoordinateSpace} (hU : IsOpen U)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) {f : ℕ → CoordinateSpace → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : TendstoUniformlyOn f (fun _ => 0) atTop (tsupport χ)) :
    Tendsto (fun n => (localized_memLp hU hχ hcχ hsχ (hf n)).toLp (fun y => χ y * f n y))
      atTop (𝓝 0) := by
  let hg : MemLp χ 2 (volume : Measure CoordinateSpace) :=
    hχ.continuous.memLp_of_hasCompactSupport hcχ
  let A := ‖hg.toLp χ‖
  have hA : 0 ≤ A := norm_nonneg _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (A+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδA : δ*(A+1) = ε := div_mul_cancel₀ _ (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hn
  have hb (y : CoordinateSpace) : |χ y * f n y| ≤ δ * |χ y| := by
    by_cases hy : y ∈ tsupport χ
    · rw [abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      simpa only [dist_zero_left, Real.norm_eq_abs] using (hn y hy).le
    · simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul, abs_zero, mul_zero, le_refl]
  have h := Burnett.X02.L2Bounds.norm_toLp_le_of_abs_le
    (localized_memLp hU hχ hcχ hsχ (hf n)) hg hδ.le hb
  rw [dist_zero_right]
  exact h.trans_lt (by change δ*A < ε; nlinarith)

theorem localized_partial_has_strong_realization {U : Set CoordinateSpace} (hU : IsOpen U)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) {f : ℕ → CoordinateSpace → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : TendstoUniformlyOn f (fun _ => 0) atTop (tsupport χ)) (v : CoordinateSpace) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) =
          ∫ y, (φ : CoordinateSpace → ℝ) y * (χ y * fderiv ℝ (f n) y v)) ∧
      Tendsto F atTop (𝓝 0) := by
  let Dχ := fun y => fderiv ℝ χ y v
  have hDχ : ContDiff ℝ ∞ Dχ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hcDχ : HasCompactSupport Dχ := hcχ.fderiv_apply ℝ v
  have hsDχ : tsupport Dχ ⊆ U := (tsupport_directional_subset χ v).trans hsχ
  let hf0 := fun n => localized_memLp hU hχ hcχ hsχ (hf n)
  let hf1 := fun n => localized_memLp hU hDχ hcDχ hsDχ (hf n)
  let F : ℕ → HminusStrongL2.Hminus := fun n =>
    HminusStrongL2.directionalFunctional v ((hf0 n).toLp (fun y => χ y * f n y)) -
      HminusStrongL2.valueFunctional ((hf1 n).toLp (fun y => Dχ y * f n y))
  refine ⟨F, ?_, ?_⟩
  · intro n φ
    change HminusStrongL2.directionalFunctional v ((hf0 n).toLp (fun y => χ y * f n y)) _ -
      HminusStrongL2.valueFunctional ((hf1 n).toLp (fun y => Dχ y * f n y)) _ = _
    rw [HminusStrongL2.directionalFunctional_test_of_smooth (hf0 n) (localized_contDiff hU hχ hsχ (hf n)),
      HminusStrongL2.valueFunctional_test (hf1 n)]
    have ha : Integrable (fun y => (φ : CoordinateSpace → ℝ) y *
        fderiv ℝ (fun x => χ x * f n x) y v) :=
      ((Burnett.X02.SobolevTestJet.test_smooth φ).continuous.mul
        (X02.CompactIBP.continuous_directional (localized_contDiff hU hχ hsχ (hf n)) v))
        |>.integrable_of_hasCompactSupport (Burnett.X02.SobolevTestJet.test_compactSupport φ).mul_right
    have hb : Integrable (fun y => (Dχ y * f n y) * (φ : CoordinateSpace → ℝ) y) :=
      ((localized_contDiff hU hDχ hsDχ (hf n)).continuous.mul
        (Burnett.X02.SobolevTestJet.test_smooth φ).continuous).integrable_of_hasCompactSupport
          hcDχ.mul_right.mul_right
    have hi := integral_sub ha hb
    rw [← hi]
    apply integral_congr_ae
    filter_upwards with y
    rw [fderiv_test_mul_local hU hχ hsχ (hf n) v y]
    dsimp only [Dχ]
    ring
  · have h0 := HminusStrongL2.directionalFunctional_tendsto_zero
      (localized_toLp_tendsto_zero hU hχ hcχ hsχ hf hu) v
    have h1 := HminusStrongL2.valueFunctional_tendsto_zero
      (localized_toLp_tendsto_zero hU hDχ hcDχ hsDχ hf (hu.mono (tsupport_directional_subset χ v)))
    simpa only [sub_zero] using h0.sub h1

theorem localized_value_has_strong_realization {U : Set CoordinateSpace} (hU : IsOpen U)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) {f : ℕ → CoordinateSpace → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : TendstoUniformlyOn f (fun _ => 0) atTop (tsupport χ)) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) =
          ∫ y, (φ : CoordinateSpace → ℝ) y * (χ y * f n y)) ∧
      Tendsto F atTop (𝓝 0) := by
  let hm := fun n => localized_memLp hU hχ hcχ hsχ (hf n)
  refine ⟨fun n => HminusStrongL2.valueFunctional ((hm n).toLp (fun y => χ y * f n y)), ?_, ?_⟩
  · intro n φ
    rw [HminusStrongL2.valueFunctional_test]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => mul_comm _ _)
  · exact HminusStrongL2.valueFunctional_tendsto_zero
      (localized_toLp_tendsto_zero hU hχ hcχ hsχ hf hu)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
variable (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
  (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
  (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
  (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
  (hconv : LocallyUniformlyConverges r g g0)
  (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
    eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
      ((ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal D)
  (c : M)
include r h0 hg hs0 hs hn0 hn hconv hb

theorem error_localized_smooth_compact_strongL2_of_original (a b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    (∀ n, ContDiff ℝ ∞ (fun y => χ y * ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d) ∧
      HasCompactSupport (fun y => χ y * ConnectionErrorLInfinity.computedError
        (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d)) ∧
    ∃ hf : ∀ n, MemLp (fun y => χ y * ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d) 2 (volume : Measure CoordinateSpace),
      Tendsto (fun n => (hf n).toLp (fun y => χ y * ConnectionErrorLInfinity.computedError
        (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d)) atTop (𝓝 0) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hE := fun n => LocalWeakRicci.computedError_component_smoothOn
    g0 (g n) h0 (hg n) hn0 (hn n) c a b d
  refine ⟨fun n => ⟨localized_contDiff hU hχ hsχ (hE n), hcχ.mul_right⟩,
    (fun n => localized_memLp hU hχ hcχ hsχ (hE n)), ?_⟩
  exact localized_toLp_tendsto_zero hU hχ hcχ hsχ hE
    (LocalWeakRicci.error_component_uniform_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d (tsupport χ) hcχ hsχ)

theorem error_localized_partial_has_strong_realization_of_original (a b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          (χ y * fderiv ℝ (fun x => ConnectionErrorLInfinity.computedError
            (coordinateBilinear g0 c) (coordinateBilinear (g n) c) x a b d) y v)) ∧
      Tendsto F atTop (𝓝 0) :=
  localized_partial_has_strong_realization (chartAt CoordinateSpace c).open_target hχ hcχ hsχ
    (fun n => LocalWeakRicci.computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d)
    (LocalWeakRicci.error_component_uniform_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d (tsupport χ) hcχ hsχ) v

theorem density_error_localized_partial_has_strong_realization_of_original (a b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
            fderiv ℝ (fun x => ConnectionErrorLInfinity.computedError
              (coordinateBilinear g0 c) (coordinateBilinear (g n) c) x a b d) y v)) ∧
      Tendsto F atTop (𝓝 0) :=
  error_localized_partial_has_strong_realization_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d
    (localized_contDiff (chartAt CoordinateSpace c).open_target hχ hsχ
      (smooth_coordinate_volume_factor g0 h0 hn0 c)) hcχ.mul_right
    (tsupport_mul_subset_left.trans hsχ) v

theorem coefficient_error_localized_value_has_strong_realization_of_original (a b d : Index)
    {χ A : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * A y) * ConnectionErrorLInfinity.computedError
            (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d)) ∧
      Tendsto F atTop (𝓝 0) :=
  localized_value_has_strong_realization (chartAt CoordinateSpace c).open_target
    (localized_contDiff (chartAt CoordinateSpace c).open_target hχ hsχ hA) hcχ.mul_right
    (tsupport_mul_subset_left.trans hsχ)
    (fun n => LocalWeakRicci.computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d)
    ((LocalWeakRicci.error_component_uniform_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d (tsupport χ) hcχ hsχ).mono tsupport_mul_subset_left)

end Burnett.Analysis.GeometricHminusRemainders
