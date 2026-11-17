import Burnett.Analysis.VacuumWeakRicci
import Burnett.Analysis.CompactRellich
import Burnett.Analysis.Sobolev.L2Bounds

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.Analysis.GeometricHminusBoundedForcing
open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci LocalWeakRicciIdentification
open Burnett.X02.SobolevTestJet

theorem all_bound_of_eventual_on_compact
    (C : ℕ → CoordinateSpace → Connection) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hC : ∀ n, ContinuousOn (C n) K) {B : ℝ} (hB : 0 ≤ B)
    (he : ∀ᶠ n in atTop, ∀ y ∈ K, ‖C n y‖ ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n y, y ∈ K → ‖C n y‖ ≤ M := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  choose b hb hbound using fun n =>
    (hK.image_of_continuousOn (hC n)).isBounded.exists_pos_norm_le
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, b n :=
    Finset.sum_nonneg (fun n _ => (hb n).le)
  refine ⟨B + ∑ n ∈ Finset.range N, b n, add_nonneg hB hsum, ?_⟩
  intro n y hy
  by_cases hn : N ≤ n
  · exact (hN n hn y hy).trans (le_add_of_nonneg_right hsum)
  · have hbn : b n ≤ ∑ i ∈ Finset.range N, b i :=
      Finset.single_le_sum (fun i _ => (hb i).le) (Finset.mem_range.mpr (not_le.mp hn))
    exact (hbound n _ (mem_image_of_mem _ hy)).trans
      (hbn.trans (le_add_of_nonneg_left hB))

theorem abs_quadraticDifference_le (C : Connection) (b d : Index) :
    |quadraticDifference C b d| ≤ 32 * ‖C‖^2 := by
  have hz : quadraticDifference (0 : Connection) b d = 0 := by simp [quadraticDifference]
  have h := abs_quadratic_difference_le C 0 b d
  simp only [hz, sub_zero, norm_zero, add_zero] at h
  nlinarith

def boundedForcing
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) (b d : Index) : ℝ :=
  -coordinateRicci (computedConnection g0) y b d -
    quadraticDifference (connectionDifference g0 g1 y) b d

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem connectionDifference_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (a b d : Index) :
    ContDiffOn ℝ ∞ (fun y => connectionDifference (coordinateBilinear g0 c)
      (coordinateBilinear g1 c) y a b d) (chartAt CoordinateSpace c).target := by
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ1 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g1 h1 hn1 c
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ1 a) b) d).sub
    (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 a) b) d)

theorem boundedForcing_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (b d : Index) :
    ContDiffOn ℝ ∞ (fun y => boundedForcing (coordinateBilinear g0 c)
      (coordinateBilinear g1 c) y b d) (chartAt CoordinateSpace c).target :=
  (coordinateRicci_component_smoothOn g0 h0 hn0 c b d).neg.sub
    (smoothOn_quadraticDifference
      (connectionDifference_component_smoothOn g0 g1 h0 h1 hn0 hn1 c) b d)

theorem exists_global_outer_cutoff (χ : D) :
    ∃ η : D, ∀ y : CoordinateSpace, (χ : CoordinateSpace → ℝ) y ≠ 0 →
      (η : CoordinateSpace → ℝ) y = 1 := by
  obtain ⟨R, hR, hχR⟩ := (test_compactSupport χ).isBounded.subset_closedBall_lt 0 (0 : CoordinateSpace)
  let η : ContDiffBump (0 : CoordinateSpace) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨⟨η, η.contDiff, η.hasCompactSupport⟩, ?_⟩
  intro y hy
  exact η.one_of_mem_closedBall (hχR (subset_tsupport (χ : CoordinateSpace → ℝ) hy))

theorem localized_boundedForcing_smooth_compact
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (b d : Index)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    ContDiff ℝ ∞ (fun y => (χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d) ∧
    HasCompactSupport (fun y => (χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d) :=
  ⟨contDiff_test_mul_local (chartAt CoordinateSpace c).open_target (test_smooth χ) hχ
    (boundedForcing_component_smoothOn g0 g1 h0 h1 hn0 hn1 c b d),
    (test_compactSupport χ).mul_right⟩

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

theorem exists_uniform_bound_connectionDifference_of_original
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n y, y ∈ K →
      ‖connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y‖ ≤ B := by
  obtain ⟨B, hB, hL⟩ := eventual_bound_linearConnection_of_original
    r g0 g h0 hg hn0 hconv hb c K hK hKt
  have hE := OriginalAdmissibleLocalControl.computedError_uniform_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c K hK hKt
  have he : ∀ᶠ n in atTop, ∀ y ∈ K,
      ‖connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y‖ ≤ B + 1 := by
    filter_upwards [hL, Metric.tendstoUniformlyOn_iff.mp hE 1 zero_lt_one] with n hnL hnE
    intro y hy
    have hEy : ‖ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y‖ ≤ 1 := by
      simpa only [dist_zero_left] using (hnE y hy).le
    have heq : connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y =
        linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y +
          ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y :=
      connection_difference_eq_linear_plus_error _ _ y
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hnL y hy) hEy)
  apply all_bound_of_eventual_on_compact _ K hK ?_ (by positivity) he
  intro n
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  apply continuousOn_pi.mpr
  intro d
  exact (connectionDifference_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d).continuousOn.mono hKt

theorem exists_uniform_bound_boundedForcing_of_original (b d : Index)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n y, y ∈ K →
      |boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d| ≤ B := by
  obtain ⟨Bconn, hC, hbound⟩ := exists_uniform_bound_connectionDifference_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c K hK hKt
  have hR := (coordinateRicci_component_smoothOn g0 h0 hn0 c b d).continuousOn.mono hKt
  obtain ⟨R, hR0, hRb⟩ := (hK.image_of_continuousOn hR).isBounded.exists_pos_norm_le
  refine ⟨R + 32 * Bconn^2, by positivity, ?_⟩
  intro n y hy
  have hRy : |coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d| ≤ R := by
    simpa only [Real.norm_eq_abs] using hRb _ (mem_image_of_mem _ hy)
  have hQ : |quadraticDifference
      (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d| ≤ 32 * Bconn^2 :=
    (abs_quadraticDifference_le _ b d).trans
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound n y hy)) (by norm_num))
  exact (abs_sub _ _).trans (by simpa only [abs_neg] using add_le_add hRy hQ)

omit r hconv hb [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem boundedForcing_eq_divergence_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (n : ℕ) (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d =
      covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
        (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
        (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c)) y) b d := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓn := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) c
  have hΓ0c (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 i) j) k
  have hΓnc (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓn i) j) k
  have hv := coordinateRicci_vacuum_identity (computedConnection (coordinateBilinear g0 c))
    (computedConnection (coordinateBilinear (g n) c)) y
    (computedConnection_torsion_free_of_symmetric g0 hs0 c y)
    (computedConnection_torsion_free_of_symmetric (g n) (hs n) c y)
    (fun i j k => ((hΓ0c i j k).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    (fun i j k => ((hΓnc i j k).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    (hVac n y hy) b d
  change 0 = coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d +
    covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
      (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
      (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c)) y) b d +
    quadraticDifference (connectionDifference (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y) b d at hv
  unfold boundedForcing
  linarith

theorem localized_boundedForcing_test_tendsto_zero_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (φ : D) : Tendsto (fun n => ∫ y, ((χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) *
      (φ : CoordinateSpace → ℝ) y) atTop (𝓝 0) := by
  have hDiv := Ricci_divergence_difference_smoothWeakZero_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d
  have h := hDiv.2 (fun y => (χ : CoordinateSpace → ℝ) y * (φ : CoordinateSpace → ℝ) y)
    ((test_smooth χ).mul (test_smooth φ)) (test_compactSupport χ).mul_right
    (tsupport_mul_subset_left.trans hχ)
  apply h.congr
  intro n
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ (chartAt CoordinateSpace c).target
  · rw [boundedForcing_eq_divergence_of_original g0 g h0 hg hs0 hs hn0 hn c hVac n y hy b d]
    ring
  · have hzero : (χ : CoordinateSpace → ℝ) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hχ h))
    simp only [hzero, zero_mul]

theorem localized_boundedForcing_uniform_L2_of_original
    (b d : Index) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    (∀ n, ContDiff ℝ ∞ (fun y => (χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) ∧
      HasCompactSupport (fun y => (χ : CoordinateSpace → ℝ) y *
        boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d)) ∧
    ∃ hf : ∀ n, MemLp (fun y => (χ : CoordinateSpace → ℝ) y *
        boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) 2
      (volume : Measure CoordinateSpace), ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      ‖(hf n).toLp (fun y => (χ : CoordinateSpace → ℝ) y *
        boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d)‖ ≤ B := by
  have hsc (n : ℕ) := localized_boundedForcing_smooth_compact g0 (g n) h0 (hg n) hn0 (hn n) c b d χ hχ
  let hf (n : ℕ) : MemLp (fun y => (χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) 2
      (volume : Measure CoordinateSpace) :=
    (hsc n).1.continuous.memLp_of_hasCompactSupport (hsc n).2
  obtain ⟨B, hB, hAb⟩ := exists_uniform_bound_boundedForcing_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d (tsupport (χ : CoordinateSpace → ℝ))
    (test_compactSupport χ) hχ
  refine ⟨hsc, hf, B * ‖valueLp χ‖, mul_nonneg hB (norm_nonneg _), ?_⟩
  intro n
  apply Burnett.X02.L2Bounds.norm_toLp_le_of_abs_le (hf n) (test_memLp χ) hB
  intro y
  by_cases hy : y ∈ tsupport (χ : CoordinateSpace → ℝ)
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hAb n y hy) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul, abs_zero, mul_zero]
    exact le_rfl

theorem localized_boundedForcing_has_strong_realization_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → (Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ),
      (∀ n (φ : D), F n (Burnett.X02.GraphDual.testMap J φ) = ∫ y,
        (φ : CoordinateSpace → ℝ) y * ((χ : CoordinateSpace → ℝ) y *
          boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d)) ∧
      Tendsto F atTop (𝓝 0) ∧ Tendsto (fun n => ‖F n‖) atTop (𝓝 0) := by
  obtain ⟨hsc, hf, B, hB, hbound⟩ := localized_boundedForcing_uniform_L2_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d χ hχ
  obtain ⟨η, hη⟩ := exists_global_outer_cutoff χ
  have hout : ∀ n y, ((χ : CoordinateSpace → ℝ) y *
      boundedForcing (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d) ≠ 0 →
      (η : CoordinateSpace → ℝ) y = 1 :=
    fun n y hy => hη y (mul_ne_zero_iff.mp hy).1
  obtain ⟨F, htest, hF, hnorm⟩ := CompactRellich.exists_sourceFunctionals_strong_zero
    (fun n => (hsc n).1) hf η hout hbound
    (localized_boundedForcing_test_tendsto_zero_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d χ hχ)
  refine ⟨F, ?_, hF, hnorm⟩
  intro n φ
  rw [htest]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => mul_comm _ _)

end OriginalData
end Burnett.Analysis.GeometricHminusBoundedForcing
