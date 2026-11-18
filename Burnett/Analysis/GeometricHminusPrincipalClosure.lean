import Burnett.Analysis.GeometricHminusCovariantRemainders
import Burnett.Analysis.GeometricPrincipalIdentity
import Burnett.Analysis.GeometricHminusBoundedForcing

set_option autoImplicit false

noncomputable section
set_option synthInstance.maxHeartbeats 200000

namespace Burnett.Analysis.GeometricHminusPrincipalClosure

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open ManifoldMetricSequence CurvatureDifference LocalWeakDerivative
open GeometricPrincipalIdentity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
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

/-- Original local physical data imply strong H⁻¹ decay of the actual paper operator,
    localized by one fixed smooth compact test cutoff in the chart target. -/
theorem linearizedRicci_has_strong_realization_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) (χ : Burnett.X02.SobolevTestJet.D)
    (hsχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D),
        Integrable (fun y => (φ : CoordinateSpace → ℝ) y *
          ((χ : CoordinateSpace → ℝ) y *
            linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d)) ∧
        F n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) =
          ∫ y, (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y *
            linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d)) ∧
      Tendsto F atTop (𝓝 0) ∧ Tendsto (fun n => ‖F n‖) atTop (𝓝 0) := by
  obtain ⟨FA, hFA, hFA0, _⟩ :=
    GeometricHminusBoundedForcing.localized_boundedForcing_has_strong_realization_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d χ hsχ
  obtain ⟨FE, hFE, hFE0⟩ :=
    GeometricHminusRemainders.Ricci_error_divergence_has_strong_realization_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d
      (Burnett.X02.SobolevTestJet.test_smooth χ)
      (Burnett.X02.SobolevTestJet.test_compactSupport χ) hsχ
  let F : ℕ → HminusStrongL2.Hminus := fun n => FA n - FE n
  have hF0 : Tendsto F atTop (𝓝 0) := by
    simpa only [sub_zero] using hFA0.sub hFE0
  refine ⟨F, ?_, hF0, ?_⟩
  · intro n φ
    let U := (chartAt CoordinateSpace c).target
    let A := GeometricHminusBoundedForcing.boundedForcing
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
    let E := ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
    let D := fun y => covariantDivergenceDifference
      (computedConnection (coordinateBilinear g0 c) y) (E y) (coordinateConnectionJet E y) b d
    have hA : ContDiffOn ℝ ∞ (fun y => A y b d) U :=
      GeometricHminusBoundedForcing.boundedForcing_component_smoothOn
        g0 (g n) h0 (hg n) hn0 (hn n) c b d
    have hD : ContDiffOn ℝ ∞ D U := by
      unfold D covariantDivergenceDifference
      exact ContDiffOn.sum (fun a _ =>
        (GeometricHminusRemainders.covariant_error_component_smoothOn
          g0 (g n) h0 (hg n) hn0 (hn n) c a a b d).sub
        (GeometricHminusRemainders.covariant_error_component_smoothOn
          g0 (g n) h0 (hg n) hn0 (hn n) c d a b a))
    have hΦ := (Burnett.X02.SobolevTestJet.test_smooth φ).mul
      (Burnett.X02.SobolevTestJet.test_smooth χ)
    have hsΦ : tsupport (fun y => (φ : CoordinateSpace → ℝ) y *
        (χ : CoordinateSpace → ℝ) y) ⊆ U := tsupport_mul_subset_right.trans hsχ
    have hIA : Integrable (fun y => (φ : CoordinateSpace → ℝ) y *
        ((χ : CoordinateSpace → ℝ) y * A y b d)) := by
      simpa only [mul_assoc] using
        (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hΦ hsΦ hA).continuous
          |>.integrable_of_hasCompactSupport
            (Burnett.X02.SobolevTestJet.test_compactSupport χ).mul_left.mul_right
    have hID : Integrable (fun y => (φ : CoordinateSpace → ℝ) y *
        ((χ : CoordinateSpace → ℝ) y * D y)) := by
      simpa only [mul_assoc] using
        (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hΦ hsΦ hD).continuous
          |>.integrable_of_hasCompactSupport
            (Burnett.X02.SobolevTestJet.test_compactSupport χ).mul_left.mul_right
    have heq (y : CoordinateSpace) : (φ : CoordinateSpace → ℝ) y *
        ((χ : CoordinateSpace → ℝ) y *
          linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) =
        (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * A y b d) -
        (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * D y) := by
      by_cases hy : y ∈ U
      · rw [linearizedRicci_eq_source_sub_error_of_coordinateVacuum
          g0 (g n) h0 (hg n) hs0 (hs n) hn0 (hn n) c y hy (hVac n y hy) b d]
        change (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y *
          (A y b d - D y)) = _
        ring
      · have hzero : (χ : CoordinateSpace → ℝ) y = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hy (hsχ h))
        simp only [hzero, zero_mul, mul_zero, sub_self]
    refine ⟨(hIA.sub hID).congr (Eventually.of_forall (fun y => (heq y).symm)), ?_⟩
    calc
      F n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) =
          FA n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) -
          FE n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) := rfl
      _ = (∫ y, (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * A y b d)) -
          ∫ y, (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * D y) := by
        rw [hFA n φ, hFE n φ]
      _ = ∫ y, (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * A y b d) -
          (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y * D y) :=
        (integral_sub hIA hID).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun y => (heq y).symm))
  · have hn : Continuous (fun H : HminusStrongL2.Hminus => ‖H‖) :=
      @continuous_norm HminusStrongL2.Hminus inferInstance
    simpa only [Function.comp_def, ContinuousLinearMap.opNorm_zero] using
      (hn.tendsto (0 : HminusStrongL2.Hminus)).comp hF0

end Burnett.Analysis.GeometricHminusPrincipalClosure
