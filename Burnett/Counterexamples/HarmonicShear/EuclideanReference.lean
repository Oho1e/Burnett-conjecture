import Burnett.Geometry.ManifoldMetricSequence
import Burnett.Geometry.IntrinsicDhMeasure

set_option autoImplicit false

noncomputable section

namespace Burnett.HarmonicShear.Reference

open Bundle Set MeasureTheory Filter LinearMap Bornology
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace Matrix
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldTensorNorm
open CovariantTensorNorm ManifoldMetricSequence

/-- The Euclidean metric on the actual tangent bundle, given by the real inner product. -/
def euclideanMetric : ManifoldMetric.Metric (M := CoordinateSpace) where
  inner _ := innerSL ℝ (E := CoordinateSpace)
  symm _ u v := real_inner_comm (F := CoordinateSpace) v u
  pos _ _ hv := (real_inner_self_pos (F := CoordinateSpace)).2 hv
  isVonNBounded _ := by
    change IsVonNBounded ℝ {v : CoordinateSpace | ⟪v, v⟫_ℝ < 1}
    have h : Metric.ball (0 : CoordinateSpace) 1 = {v : CoordinateSpace | ⟪v, v⟫_ℝ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √ 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← h]
    exact NormedSpace.isVonNBounded_ball ℝ CoordinateSpace 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ (E := CoordinateSpace))
    ext u v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.linearMapAt_apply, TangentSpace]

theorem euclideanMetric_inner (x u v : CoordinateSpace) : euclideanMetric.inner x u v = ⟪u, v⟫_ℝ := rfl

theorem chart_self_apply (c x : CoordinateSpace) : chartAt CoordinateSpace c x = x := by
  rw [chartAt_self_eq]
  rfl

theorem chart_self_symm_apply (c x : CoordinateSpace) : (chartAt CoordinateSpace c).symm x = x := by
  rw [chartAt_self_eq]
  rfl

theorem chart_self_source (c : CoordinateSpace) : (chartAt CoordinateSpace c).source = Set.univ := by
  rw [chartAt_self_eq]
  rfl

theorem chart_self_target (c : CoordinateSpace) : (chartAt CoordinateSpace c).target = Set.univ := by
  rw [chartAt_self_eq]
  rfl

theorem tangentFrame_self (c x u : CoordinateSpace) : tangentFrame c x u = u := by
  rw [tangentFrame, TangentBundle.symmL_model_space]
  rfl

theorem coordinateMetric_euclidean_apply (c x u v : CoordinateSpace) :
    coordinateMetric euclideanMetric c x u v = ⟪u, v⟫_ℝ := by
  change euclideanMetric.inner ((chartAt CoordinateSpace c).symm x)
      (tangentFrame c ((chartAt CoordinateSpace c).symm x) u)
      (tangentFrame c ((chartAt CoordinateSpace c).symm x) v) = _
  rw [tangentFrame_self, tangentFrame_self, euclideanMetric_inner]

theorem coordinateMetric_euclidean_components (c x : CoordinateSpace) :
    metricComponents (coordinateMetric euclideanMetric c) x = (1 : Matrix Index Index ℝ) := by
  ext i j
  change coordinateMetric euclideanMetric c x (coordinateBasis i) (coordinateBasis j) = _
  rw [coordinateMetric_euclidean_apply]
  simp [coordinateBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, Matrix.one_apply]

theorem coordinateMetric_euclidean_jet (c x : CoordinateSpace) :
    coordinateJet (metricComponents (coordinateMetric euclideanMetric c)) x = 0 := by
  funext d i j
  simp [coordinateJet, coordinateMetric_euclidean_components]

theorem coordinateMetric_euclidean_connection (c x : CoordinateSpace) :
    BackgroundConnection.computedConnection (coordinateMetric euclideanMetric c) x = 0 := by
  rw [BackgroundConnection.computedConnection, coordinateMetric_euclidean_jet]
  funext a b d
  simp [christoffel, koszul]

end Burnett.HarmonicShear.Reference

namespace Burnett.HarmonicShear.Reference

open Bundle Set MeasureTheory Filter LinearMap
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace Matrix BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldTensorNorm
open CovariantTensorNorm ManifoldMetricSequence

private def basisBilinear (i j : Index) : CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) i).smulRight
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) j)

private def coordinateCLM (G : CoordinateSpace → Tensor2) (x : CoordinateSpace) :
    CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ :=
  ∑ i : Index, ∑ j : Index, G x i j • basisBilinear i j

/-- Assemble a coordinate family into actual continuous tangent-fiber forms on Euclidean space. -/
def fieldOfComponents (G : CoordinateSpace → Tensor2) :
    ManifoldBilinear.Field (M := CoordinateSpace) :=
  fun x => coordinateCLM G x

theorem fieldOfComponents_apply (G : CoordinateSpace → Tensor2) (x u v : CoordinateSpace) :
    fieldOfComponents G x u v = Matrix.toBilin coordinateBasis (G x) u v := by
  change coordinateCLM G x u v = _
  unfold coordinateCLM
  simp [basisBilinear, Matrix.toBilin_apply, coordinateBasis, EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.sum_apply, mul_comm, mul_left_comm]

theorem coordinateBilinear_fieldOfComponents (G : CoordinateSpace → Tensor2) (c x : CoordinateSpace) :
    coordinateBilinear (fieldOfComponents G) c x = Matrix.toBilin coordinateBasis (G x) := by
  ext u v
  change fieldOfComponents G ((chartAt CoordinateSpace c).symm x)
    (tangentFrame c ((chartAt CoordinateSpace c).symm x) u)
    (tangentFrame c ((chartAt CoordinateSpace c).symm x) v) = _
  rw [chart_self_symm_apply, tangentFrame_self, tangentFrame_self, fieldOfComponents_apply]

theorem coordinateComponents_fieldOfComponents (G : CoordinateSpace → Tensor2) (c x : CoordinateSpace) :
    metricComponents (coordinateBilinear (fieldOfComponents G) c) x = G x := by
  have hmat : metricComponents (coordinateBilinear (fieldOfComponents G) c) x =
      BilinForm.toMatrix coordinateBasis (coordinateBilinear (fieldOfComponents G) c x) := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
  rw [hmat, coordinateBilinear_fieldOfComponents, ← BilinForm.toMatrix_symm,
    LinearEquiv.apply_symm_apply]

theorem fieldOfComponents_isSmooth (G : CoordinateSpace → Tensor2)
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j)) :
    ManifoldBilinear.IsSmooth (fieldOfComponents G) := by
  have h : ContDiff ℝ ∞ (coordinateCLM G) := by
    unfold coordinateCLM
    exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hG i j).smul contDiff_const
  intro x
  rw [contMDiffAt_section]
  convert h.contMDiff.contMDiffAt using 1
  ext u v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivialization.linearMapAt_apply, fieldOfComponents, TangentSpace]


theorem fieldOfComponents_isSymmetric (G : CoordinateSpace → Tensor2)
    (hG : ∀ x i j, G x i j = G x j i) : ManifoldBilinear.IsSymmetric (fieldOfComponents G) := by
  intro x u v
  simp only [fieldOfComponents_apply, Matrix.toBilin_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hG x i j]
  ring

theorem fieldOfComponents_isNondegenerate (G : CoordinateSpace → Tensor2)
    (hG : ∀ x, Matrix.det (G x) ≠ 0) :
    ManifoldBilinear.IsNondegenerate (fieldOfComponents G) := by
  intro x u hu
  have hn : (Matrix.toBilin coordinateBasis (G x)).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ coordinateBasis
    rw [← BilinForm.toMatrix_symm, LinearEquiv.apply_symm_apply]
    exact hG x
  exact hn u (fun v => (fieldOfComponents_apply G x u v).symm.trans (hu v))

theorem coordinateComponents_field_difference (G H : CoordinateSpace → Tensor2)
    (c : CoordinateSpace) :
    metricComponents (coordinateBilinear (fieldOfComponents G - fieldOfComponents H) c) =
      fun x => G x - H x := by
  funext x
  rw [coordinateComponents_sub, coordinateComponents_fieldOfComponents,
    coordinateComponents_fieldOfComponents]

theorem physicalNorm2_field_difference (G H : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) :
    physicalNorm2 euclideanMetric (fieldOfComponents G - fieldOfComponents H) x =
      norm2 (1 : Matrix Index Index ℝ) (G x - H x) := by
  have hx : x ∈ (chartAt CoordinateSpace x).target := by simp
  have h := physicalNorm2_eq_coordinate euclideanMetric
    (fieldOfComponents G - fieldOfComponents H) x hx
  simpa only [chart_self_symm_apply, coordinateMetric_euclidean_components,
    coordinateComponents_field_difference] using h

theorem coordinateDerivativeTensor_field_difference (G H : CoordinateSpace → Tensor2)
    (c x : CoordinateSpace) :
    IntrinsicDhMeasure.coordinateDerivativeTensor euclideanMetric
      (fieldOfComponents G - fieldOfComponents H) c x =
      coordinateJet (fun y => G y - H y) x := by
  rw [IntrinsicDhMeasure.coordinateDerivativeTensor, coordinateMetric_euclidean_connection,
    coordinateComponents_field_difference]
  funext d i j
  simp [covariantJet]

theorem normScalar_field_difference (G H : CoordinateSpace → Tensor2)
    (hG : ManifoldBilinear.IsSmooth (fieldOfComponents G))
    (hH : ManifoldBilinear.IsSmooth (fieldOfComponents H))
    (x : CoordinateSpace) :
    IntrinsicDhMeasure.normScalar euclideanMetric (fieldOfComponents G - fieldOfComponents H) x =
      norm3 (1 : Matrix Index Index ℝ) (coordinateJet (fun y => G y - H y) x) := by
  have h := IntrinsicDhMeasure.normScalar_eq_chart euclideanMetric
    (fieldOfComponents G - fieldOfComponents H)
    (IntrinsicCov2.isSmooth_difference _ _ hG hH) x x (mem_chart_source CoordinateSpace x)
  simpa only [chart_self_apply, coordinateMetric_euclidean_components,
    coordinateDerivativeTensor_field_difference] using h

theorem locallyUniformlyConverges_fieldOfComponents (G : ℕ → CoordinateSpace → Tensor2)
    (H : CoordinateSpace → Tensor2)
    (h : ∀ S : Set CoordinateSpace, IsCompact S → TendstoUniformlyOn
      (fun n x => norm2 (1 : Matrix Index Index ℝ) (G n x - H x)) (fun _ => 0) atTop S) :
    LocallyUniformlyConverges euclideanMetric (fun n => fieldOfComponents (G n)) (fieldOfComponents H) := by
  intro S hS
  simpa only [physicalNorm2_field_difference] using h S hS

theorem intrinsicDh_eLpNorm_bound_of_coordinateJet
    (G : ℕ → CoordinateSpace → Tensor2) (H : CoordinateSpace → Tensor2)
    (hG : ∀ n, ManifoldBilinear.IsSmooth (fieldOfComponents (G n)))
    (hH : ManifoldBilinear.IsSmooth (fieldOfComponents H))
    (μ : Measure CoordinateSpace) (S : Set CoordinateSpace) (hS : MeasurableSet S)
    (C : ℝ) (h : ∀ n x, x ∈ S →
      norm3 (1 : Matrix Index Index ℝ) (coordinateJet (fun y => G n y - H y) x) ≤ C) :
    ∀ n, eLpNorm (IntrinsicDhMeasure.normScalar euclideanMetric
        (fieldOfComponents (G n) - fieldOfComponents H)) ∞ (μ.restrict S) ≤ ENNReal.ofReal C := by
  intro n
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [Real.norm_eq_abs, normScalar_field_difference _ _ (hG n) hH]
  have hnonneg : 0 ≤ norm3 (1 : Matrix Index Index ℝ)
      (coordinateJet (fun y => G n y - H y) x) := Real.sqrt_nonneg _
  rw [abs_of_nonneg hnonneg]
  exact h n x hx


/-- For unit absolute determinant, the actual manifold volume is Euclidean volume. -/
theorem geometricMeasure_fieldOfComponents_eq_volume (G : CoordinateSpace → Tensor2)
    (hG : ∀ x, |Matrix.det (G x)| = 1) :
    ManifoldVolume.geometricMeasure (fieldOfComponents G) = (volume : Measure CoordinateSpace) := by
  let c : CoordinateSpace := 0
  have hchart : (chartAt CoordinateSpace c : CoordinateSpace → CoordinateSpace) = id :=
    funext (chart_self_apply c)
  have hρ : LorentzVolume.density (metricComponents (coordinateBilinear (fieldOfComponents G) c)) = 1 := by
    funext x
    simp only [LorentzVolume.density, coordinateComponents_fieldOfComponents, hG x,
      Real.sqrt_one, ENNReal.ofReal_one, Pi.one_apply]
  have h := ManifoldVolume.map_chart_geometricMeasure (fieldOfComponents G) c
  simpa only [hchart, chart_self_source, chart_self_target, Measure.restrict_univ, Measure.map_id,
    ManifoldVolume.coordinateMeasure, LorentzVolume.coordinateMeasure, hρ, withDensity_one] using h

/-- Compact coordinate-jet bounds imply the project’s physical essential bound. -/
theorem intrinsicDh_compact_bounds_of_coordinateJet
    (G : ℕ → CoordinateSpace → Tensor2) (H : CoordinateSpace → Tensor2)
    (hG : ∀ n, ManifoldBilinear.IsSmooth (fieldOfComponents (G n)))
    (hH : ManifoldBilinear.IsSmooth (fieldOfComponents H))
    (h : ∀ S : Set CoordinateSpace, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ S →
      norm3 (1 : Matrix Index Index ℝ) (coordinateJet (fun y => G n y - H y) x) ≤ C) :
    ∀ S : Set CoordinateSpace, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar euclideanMetric
        (fieldOfComponents (G n) - fieldOfComponents H)) ∞
        ((ManifoldVolume.geometricMeasure (fieldOfComponents H)).restrict S) ≤ ENNReal.ofReal C := by
  intro S hS
  obtain ⟨C, hC, hb⟩ := h S hS
  exact ⟨C, hC, intrinsicDh_eLpNorm_bound_of_coordinateJet G H hG hH _ S hS.measurableSet C hb⟩

end Burnett.HarmonicShear.Reference
