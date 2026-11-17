import Burnett.Analysis.VacuumWeakRicci

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.LocalWeakRicciIdentification

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem coordinateMeasure_test_integral_eq
    (B : Field (M := M)) (hB : IsSmooth B) (c : M) {ψ : CoordinateSpace → ℝ}
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) (F : CoordinateSpace → ℝ) :
    (∫ y, ψ y * F y ∂(ManifoldVolume.coordinateMeasure B c)) =
      ∫ y, (ψ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B c) y)|) * F y := by
  let U := (chartAt CoordinateSpace c).target
  let G := metricComponents (coordinateBilinear B c)
  have hU : MeasurableSet U := (chartAt CoordinateSpace c).open_target.measurableSet
  have hm := LorentzVolume.aemeasurable_density_restrict (volume : Measure CoordinateSpace) G U hU
    (ManifoldBilinear.continuousOn_components B hB c)
  have ht : ∀ᵐ y ∂(volume : Measure CoordinateSpace).restrict U, LorentzVolume.density G y < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hm ht (fun y => ψ y * F y) hU
  have hz (y : CoordinateSpace) (hy : y ∉ U) : ψ y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hsψ h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp only [hz y hy, zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp only [hz y hy, zero_mul, smul_zero])] at h
  change (∫ y, ψ y * F y ∂(ManifoldVolume.coordinateMeasure B c)) = _ at h
  apply h.trans
  apply integral_congr_ae
  filter_upwards with y
  simp only [LorentzVolume.density, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]
  dsimp only [G]
  ring

omit [MeasurableSpace M] [BorelSpace M] in
theorem coordinateMeasure_test_integrable
    (B : Field (M := M)) (hB : IsSmooth B) (c : M) {ψ F : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (hF : ContDiffOn ℝ ∞ F (chartAt CoordinateSpace c).target) :
    Integrable (fun y => ψ y * F y) (ManifoldVolume.coordinateMeasure B c) := by
  let μ := ManifoldVolume.coordinateMeasure B c
  have hK := ManifoldVolumeRegularity.coordinateMeasure_compact_lt_top B hB c hcψ hsψ
  letI : IsFiniteMeasure (μ.restrict (tsupport ψ)) := ⟨by simpa only [Measure.restrict_apply_univ] using hK⟩
  have hi : Integrable (fun y => ψ y * F y) (μ.restrict (tsupport ψ)) :=
    (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hψ hsψ hF).continuous
      |>.integrable_of_hasCompactSupport hcψ.mul_right
  exact (integrableOn_iff_integrable_of_support_subset
    (fun y hy => (subset_tsupport ψ) (by exact (mul_ne_zero_iff.mp hy).1))).mp hi

variable [SecondCountableTopology M]

theorem vacuum_Ricci_coordinateMeasure_limit_of_original
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal D)
    (c : M) (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) {ψ : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    (∀ n, Integrable (fun y => ψ y * (-quadraticDifference
      (linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d))
      (ManifoldVolume.coordinateMeasure g0 c)) ∧
    Integrable (fun y => ψ y * coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d)
      (ManifoldVolume.coordinateMeasure g0 c) ∧
    Tendsto (fun n => ∫ y, ψ y * (-quadraticDifference
      (linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d)
      ∂(ManifoldVolume.coordinateMeasure g0 c)) atTop
      (𝓝 (∫ y, ψ y * coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d
        ∂(ManifoldVolume.coordinateMeasure g0 c))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact coordinateMeasure_test_integrable g0 h0 c hψ hcψ hsψ
      ((smoothOn_quadraticDifference (linearConnection_component_smoothOn
        g0 (g n) h0 (hg n) hn0 (hn n) c) b d).neg)
  · exact coordinateMeasure_test_integrable g0 h0 c hψ hcψ hsψ
      (coordinateRicci_component_smoothOn g0 h0 hn0 c b d)
  · have h := vacuum_Ricci_negative_quadratic_test_limit_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d hψ hcψ hsψ
    have heq (n : ℕ) := coordinateMeasure_test_integral_eq g0 h0 c hsψ
      (fun y => -quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d)
    have htarget := coordinateMeasure_test_integral_eq g0 h0 c hsψ
      (fun y => coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d)
    simp_rw [heq]
    rw [htarget]
    exact h

end Burnett.Analysis.LocalWeakRicciIdentification
