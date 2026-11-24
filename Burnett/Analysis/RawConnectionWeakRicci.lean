import Burnett.Analysis.MeasureWeakRicci

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.PartialJetReplacement

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci LocalWeakRicciIdentification

/-- The Christoffel-linear expression made from the actual raw derivative
of the metric difference, with the same fixed background inverse. -/
def rawLinearConnection
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) : Connection :=
  christoffel (matrixInverse (metricComponents g0 y))
    (coordinateJet (fun x => metricComponents g1 x - metricComponents g0 x) y)

theorem christoffel_sub_jet (G : Tensor2) (J K : FirstJet) :
    christoffel G J - christoffel G K = christoffel G (J - K) := by
  funext a b c
  simp only [christoffel, koszul_sub, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

theorem norm_covariantJet_sub_raw_le (Γ : Connection) (h : Tensor2) (J : FirstJet) :
    ‖covariantJet Γ h J - J‖ ≤ 8 * ‖Γ‖ * ‖h‖ := by
  apply ConnectionError.norm_connection_le_of_entries _ (by positivity)
  intro a b c
  have heq : (covariantJet Γ h J - J) a b c =
      -(∑ e, Γ e a b * h e c) - ∑ e, Γ e a c * h b e := by
    simp only [covariantJet, Pi.sub_apply]
    ring
  rw [heq]
  have h1 := PerturbationJet.abs_connection_contract_le Γ h a b c
  have h2 := PerturbationJet.abs_connection_contract_right_le Γ h a b c
  have h := abs_sub (-(∑ e, Γ e a b * h e c)) (∑ e, Γ e a c * h b e)
  rw [abs_neg] at h
  linarith

theorem norm_rawLinearConnection_sub_linear_le
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) :
    ‖rawLinearConnection g0 g1 y - linearConnection g0 g1 y‖ ≤
      (48 * ‖matrixInverse (metricComponents g0 y)‖ * ‖computedConnection g0 y‖) *
        ‖metricComponents g1 y - metricComponents g0 y‖ := by
  rw [norm_sub_rev]
  unfold rawLinearConnection linearConnection
  rw [christoffel_sub_jet]
  have h := norm_covariantJet_sub_raw_le (computedConnection g0 y)
    (metricComponents g1 y - metricComponents g0 y)
    (coordinateJet (fun x => metricComponents g1 x - metricComponents g0 x) y)
  calc
    _ ≤ 6 * ‖matrixInverse (metricComponents g0 y)‖ *
        ‖auxiliaryPerturbationJet g0 g0 g1 y -
          coordinateJet (fun x => metricComponents g1 x - metricComponents g0 x) y‖ :=
      ConnectionError.norm_christoffel_le _ _
    _ ≤ 6 * ‖matrixInverse (metricComponents g0 y)‖ *
        (8 * ‖computedConnection g0 y‖ * ‖metricComponents g1 y - metricComponents g0 y‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem rawLinearConnection_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (c : M) (a b d : Index) :
    ContDiffOn ℝ ∞ (fun y => rawLinearConnection (coordinateBilinear g0 c)
      (coordinateBilinear g1 c) y a b d) (chartAt CoordinateSpace c).target := by
  let U := (chartAt CoordinateSpace c).target
  have hG0 := ManifoldBilinear.contDiffOn_metricComponents g0 h0 c
  have hG1 := ManifoldBilinear.contDiffOn_metricComponents g1 h1 c
  have hH (i j : Index) : ContDiffOn ℝ ∞ (fun y =>
      (metricComponents (coordinateBilinear g1 c) y -
        metricComponents (coordinateBilinear g0 c) y) i j) U :=
    (hG1 i j).sub (hG0 i j)
  have hJ := SmoothMetricConnection.contDiffOn_coordinateJet _ U
    (chartAt CoordinateSpace c).open_target hH
  have hi (i j : Index) := SmoothMetricConnection.contDiffOn_matrixInverse
    (metricComponents (coordinateBilinear g0 c)) U hG0
    (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c hy) i j
  unfold rawLinearConnection christoffel koszul
  exact ContDiffOn.sum (fun e _ => (hi a e).mul
    ((((hJ b d e).add (hJ d b e)).sub (hJ e b d)).div_const 2))

section OriginalData
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
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

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] hg hs0 hs hn hb in
theorem rawLinearConnection_sub_linear_uniform_of_original
    (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n y => rawLinearConnection (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y -
      linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
      (fun _ => 0) atTop K := by
  have hcomp := (BackgroundConnection.continuousOn_components_of_contDiffOn
    (metricComponents (coordinateBilinear g0 c)) _
      (ManifoldBilinear.contDiffOn_metricComponents_one g0 h0 c)).mono hKt
  obtain ⟨B, hB, hInv⟩ := InverseField.exists_pos_bound_matrixInverse
    (metricComponents (coordinateBilinear g0 c)) K hK hcomp
    (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c (hKt hy))
  have hΓ := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c).continuousOn.mono hKt
  obtain ⟨G, hG, hΓb⟩ := (hK.image_of_continuousOn hΓ).isBounded.exists_pos_norm_le
  apply ConnectionError.tendstoUniformlyOn_zero_of_eventually_norm_le_dist
    (components_uniform_of_physical_C0loc r g g0 hconv c K hK hKt)
    (C := 48 * B * G) (by positivity)
  apply Eventually.of_forall
  intro n y hy
  have hΓy : ‖computedConnection (coordinateBilinear g0 c) y‖ ≤ G :=
    hΓb _ (mem_image_of_mem _ hy)
  rw [dist_eq_norm]
  exact (norm_rawLinearConnection_sub_linear_le _ _ y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left (hInv y hy) (by norm_num)) hΓy
        (norm_nonneg _) (by positivity)) (norm_nonneg _))

omit hs0 hs hn in
theorem raw_quadratic_replacement_uniform_of_original (b d : Index)
    (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n y =>
      quadraticDifference (rawLinearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d -
      quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d) (fun _ => 0) atTop K := by
  obtain ⟨B, hB, hL⟩ := eventual_bound_linearConnection_of_original
    r g0 g h0 hg hn0 hconv hb c K hK hKt
  apply quadratic_replacement_uniform (fun n y => ?_)
    (rawLinearConnection_sub_linear_uniform_of_original r g0 g h0 hn0 hconv c K hK hKt) hB hL b d
  abel

end OriginalData
end Burnett.Analysis.PartialJetReplacement

namespace Burnett.Analysis.PartialJetReplacement

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci LocalWeakRicciIdentification

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

omit hs0 hs in
theorem raw_quadratic_replacement_coordinateMeasure_test_of_original (b d : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, ψ y *
      (quadraticDifference (rawLinearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d -
      quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d)
        ∂(ManifoldVolume.coordinateMeasure g0 c)) atTop (𝓝 0) := by
  have h := integral_test_local_tendsto_zero (chartAt CoordinateSpace c).open_target
    (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hψ hsψ
      (smooth_coordinate_volume_factor g0 h0 hn0 c)) hcψ.mul_right
    (tsupport_mul_subset_left.trans hsψ)
    (fun n => (smoothOn_quadraticDifference
      (rawLinearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 c) b d).sub
      (smoothOn_quadraticDifference
        (linearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c) b d))
    (raw_quadratic_replacement_uniform_of_original r g0 g h0 hg hn0 hconv hb c b d)
  have heq (n : ℕ) := coordinateMeasure_test_integral_eq g0 h0 c hsψ
    (fun y => quadraticDifference (rawLinearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d -
      quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d)
  simp_rw [heq]
  exact h

/-- The original vacuum weak-Ricci limit now uses the actual partial first
jet, with exactly the same compact test and background volume measure. -/
theorem vacuum_Ricci_raw_coordinateMeasure_limit_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) {ψ : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    (∀ n, Integrable (fun y => ψ y * (-quadraticDifference
      (rawLinearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d))
        (ManifoldVolume.coordinateMeasure g0 c)) ∧
    Integrable (fun y => ψ y * coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d)
      (ManifoldVolume.coordinateMeasure g0 c) ∧
    Tendsto (fun n => ∫ y, ψ y * (-quadraticDifference
      (rawLinearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d)
        ∂(ManifoldVolume.coordinateMeasure g0 c)) atTop
      (𝓝 (∫ y, ψ y * coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d
        ∂(ManifoldVolume.coordinateMeasure g0 c))) := by
  obtain ⟨hiL, hiR, hlim⟩ := vacuum_Ricci_coordinateMeasure_limit_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d hψ hcψ hsψ
  have hQraw (n : ℕ) := smoothOn_quadraticDifference
    (rawLinearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 c) b d
  have hQlinear (n : ℕ) := smoothOn_quadraticDifference
    (linearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c) b d
  have hiRaw (n : ℕ) := coordinateMeasure_test_integrable g0 h0 c hψ hcψ hsψ (hQraw n).neg
  have hiDiff (n : ℕ) := coordinateMeasure_test_integrable g0 h0 c hψ hcψ hsψ
    ((hQraw n).sub (hQlinear n))
  have h := hlim.sub (raw_quadratic_replacement_coordinateMeasure_test_of_original
    r g0 g h0 hg hn0 hn hconv hb c b d hψ hcψ hsψ)
  simp only [sub_zero] at h
  refine ⟨hiRaw, hiR, h.congr ?_⟩
  intro n
  have heq : (fun y => ψ y * (-quadraticDifference
        (rawLinearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d)) =
      (fun y => ψ y * (-quadraticDifference
        (linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d)) -
      (fun y => ψ y *
        (quadraticDifference (rawLinearConnection (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c) y) b d -
        quadraticDifference (linearConnection (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c) y) b d)) := by
    funext y
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (integral_sub (hiL n) (hiDiff n)).symm

end Burnett.Analysis.PartialJetReplacement
