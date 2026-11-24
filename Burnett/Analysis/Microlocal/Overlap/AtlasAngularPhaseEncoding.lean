import Burnett.Analysis.Microlocal.Overlap.AtlasChartAmplitudeIntegrability
import Burnett.Geometry.Cotangent.FixedChartNaturality
import Burnett.Analysis.Microlocal.Overlap.AmplitudeEntryRecovery
import Burnett.Counterexamples.Bianchi.UnitNormalization

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric MaximalChart UnitNullCompactness
open UnitCosphere (Cosphere projection)
open CotangentUnitNormalization (unitShell_punctured)
open ChartVolume (derivativeMatrix)
open FixedCotangentChart
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.OverlapCovectors (tensorPairTransition tensorJetTransition jetCovariance_tensor_transition)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeCovarianceDensity chartTangentBasis chartTangentBasis_apply fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot gradientEmbedding gradient_factor_entry)
open Burnett.Microlocal.FixedChartGeometricDensity
  (auxiliaryScale auxiliaryScale_pos auxiliaryUnitCovector roundCovector)
open scoped ComplexConjugate ContDiff Manifold Matrix

abbrev AtlasAngularSphere := Metric.sphere (0 : CoordinateSpace) 1
abbrev AtlasAngularPhase := CoordinateSpace × AtlasAngularSphere

private def nonzeroAngularRepresentative (v : CoordinateSpace) : CoordinateSpace :=
  if v = 0 then coordinateBasis 0 else v

private theorem nonzeroAngularRepresentative_ne_zero (v : CoordinateSpace) :
    nonzeroAngularRepresentative v ≠ 0 := by
  by_cases hv : v = 0
  · simpa only [nonzeroAngularRepresentative, if_pos hv] using coordinateBasis.ne_zero 0
  · simpa only [nonzeroAngularRepresentative, if_neg hv] using hv

/-- Round normalization of a real covector, with a Borel value assigned at zero. -/
def atlasAngularDirection (v : CoordinateSpace) : AtlasAngularSphere := by
  let u := nonzeroAngularRepresentative v
  have hu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr (nonzeroAngularRepresentative_ne_zero v)
  refine ⟨‖u‖⁻¹ • u, ?_⟩
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hu]

theorem atlasAngularDirection_value {v : CoordinateSpace} (hv : v ≠ 0) :
    (atlasAngularDirection v).val = ‖v‖⁻¹ • v := by
  change ‖nonzeroAngularRepresentative v‖⁻¹ • nonzeroAngularRepresentative v = _
  rw [nonzeroAngularRepresentative, if_neg hv]

theorem atlasAngularDirection_measurable : Measurable atlasAngularDirection := by
  have h : Measurable nonzeroAngularRepresentative := by
    unfold nonzeroAngularRepresentative
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id
  exact (h.norm.inv.smul h).subtype_mk

theorem atlasAngularDirection_pos_smul {v : CoordinateSpace} (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) :
    atlasAngularDirection (s • v) = atlasAngularDirection v := by
  apply Subtype.ext
  rw [atlasAngularDirection_value (smul_ne_zero hs.ne' hv), atlasAngularDirection_value hv]
  simp only [norm_smul, Real.norm_of_nonneg hs.le, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hs.ne', mul_one]

theorem atlasAngularDirection_sphere (v : AtlasAngularSphere) : atlasAngularDirection v.val = v := by
  have hNorm : ‖v.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hv : v.val ≠ 0 := norm_ne_zero_iff.mp (hNorm.symm ▸ one_ne_zero)
  apply Subtype.ext
  rw [atlasAngularDirection_value hv, hNorm, inv_one, one_smul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The coordinates of the actual auxiliary unit covector in a fixed atlas chart. -/
def atlasChartUnitCovector {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r) : Covector :=
  (fixedChartPhase c p.val).2

theorem atlasChartUnitCovector_of_mem {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) (i : Index) :
    atlasChartUnitCovector c p i = fixedCovector c p.val (coordinateBasis i) := by
  unfold atlasChartUnitCovector
  rw [fixedChartPhase_of_mem c p.val hp]

theorem atlasChartUnitCovector_ne_zero {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) : atlasChartUnitCovector c p ≠ 0 := by
  intro hZero
  have h : p.val.2.toLinearMap = 0 := by
    apply (chartTangentBasis c (projection p) hp).ext
    intro i
    change p.val.2 (chartTangentBasis c (projection p) hp i) = 0
    rw [chartTangentBasis_apply]
    exact (atlasChartUnitCovector_of_mem c p hp i).symm.trans (congrFun hZero i)
  exact unitShell_punctured r p.property (ContinuousLinearMap.ext (fun v => DFunLike.congr_fun h v))

theorem atlasChartUnitCovector_change {r : Metric (M := M)} (c d : AtlasChart M) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    atlasChartUnitCovector d p = fixedCotangentTransitionMatrix c d (projection p) *ᵥ
      atlasChartUnitCovector c p := by
  funext i
  let x := projection p
  let L := fderiv ℝ (d.transition c) (d.chart x)
  let ξ := fixedCovector c p.val
  rw [atlasChartUnitCovector_of_mem d p hd]
  have hFrame := inverseFrame_change c d x hc hd
  have hEntry : fixedCovector d p.val (coordinateBasis i) = ξ (L (coordinateBasis i)) := by
    change p.val.2 (inverseFrame d x (coordinateBasis i)) =
      p.val.2 (inverseFrame c x (L (coordinateBasis i)))
    rw [hFrame]
    rfl
  rw [hEntry]
  have hSum := congrArg ξ (coordinateBasis.sum_repr (L (coordinateBasis i)))
  simp only [map_sum, map_smul, smul_eq_mul] at hSum
  refine hSum.symm.trans ?_
  simp only [Matrix.mulVec, dotProduct, fixedCotangentTransitionMatrix, Matrix.transpose_apply,
    derivativeMatrix, LinearMap.toMatrix_apply, atlasChartUnitCovector_of_mem c p hc]
  rfl

/-- The true receiving phase uses the round representative of the actual
auxiliary unit covector while retaining its base coordinates. -/
def atlasAngularPhaseCode {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r) : AtlasAngularPhase :=
  ((fixedChartPhase c p.val).1, atlasAngularDirection (WithLp.toLp 2 (atlasChartUnitCovector c p)))

theorem atlasAngularPhaseCode_measurable (r : Metric (M := M)) (c : AtlasChart M) :
    Measurable (atlasAngularPhaseCode (r := r) c) := by
  have h := measurable_fixedChartPhase_comp (Subtype.val : Cosphere r → CotangentBundle M)
    continuous_subtype_val c
  exact h.fst.prodMk (atlasAngularDirection_measurable.comp
    ((PiLp.continuous_toLp 2 (fun _ : Index => ℝ)).measurable.comp h.snd))

theorem atlasChartUnitCovector_preferred_ray (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) :
    atlasChartUnitCovector (.atPoint q.center) (chartAuxiliaryCosphere r q z) =
      auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z) := by
  have hz : (chartAuxiliaryRay r q z).proj ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  change (fixedChartPhase (.atPoint q.center) (chartAuxiliaryRay r q z)).2 = _
  rw [fixedChartPhase_preferred q.center _ hz, chartAuxiliaryRay_coords]

theorem atlasAngularPhaseCode_preferred_ray (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) :
    atlasAngularPhaseCode (.atPoint q.center) (chartAuxiliaryCosphere r q z) = (z.1.val, z.2) := by
  have hz : (chartAuxiliaryRay r q z).proj ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  apply Prod.ext
  · change (fixedChartPhase (.atPoint q.center) (chartAuxiliaryRay r q z)).1 = z.1.val
    rw [fixedChartPhase_preferred q.center _ hz]
    exact (chartAt CoordinateSpace q.center).right_inv (q.ball_in_chart z.1.property)
  · have hη : WithLp.toLp 2 (auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)) =
        auxiliaryScale (chartAuxiliaryInverse r q z.1) (roundCovector z) • (z.2 : CoordinateSpace) :=
      PiLp.ext (fun _ => rfl)
    have hNorm : ‖(z.2 : CoordinateSpace)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
    have hNonzero : (z.2 : CoordinateSpace) ≠ 0 := norm_ne_zero_iff.mp (hNorm.symm ▸ one_ne_zero)
    change atlasAngularDirection (WithLp.toLp 2
      (atlasChartUnitCovector (.atPoint q.center) (chartAuxiliaryCosphere r q z))) = z.2
    rw [atlasChartUnitCovector_preferred_ray, hη,
      atlasAngularDirection_pos_smul hNonzero (auxiliaryScale_pos _ _ (chartAuxiliaryNorm_pos r q z)),
      atlasAngularDirection_sphere]

/-- Operator-second jet entry, with both real unit-covector factors. -/
def atlasOrderedJetEntry {r : Metric (M := M)} (c : AtlasChart M) (A : AmplitudeCovarianceDensity r)
    (p : Cosphere r) (i j : JetSlot) : ℂ :=
  (atlasChartUnitCovector c p i.1 : ℂ) * (atlasChartUnitCovector c p j.1 : ℂ) *
    atlasAmplitudeMatrix c A p j.2 i.2

/-- The same three-slot congruence in the operator-second entry convention. -/
theorem atlasOrderedJetEntry_change {r : Metric (M := M)} (c d : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) (i j : JetSlot) :
    let C := tensorJetTransition (fixedCotangentTransitionMatrix c d (projection p))
    atlasOrderedJetEntry d A p i j =
      ∑ k : JetSlot, ∑ l : JetSlot, conj (C i k) * C j l * atlasOrderedJetEntry c A p k l := by
  intro C
  let T := fixedCotangentTransitionMatrix c d (projection p)
  let η := atlasChartUnitCovector c p
  let η' := atlasChartUnitCovector d p
  let S := atlasAmplitudeMatrix c A p
  let S' := atlasAmplitudeMatrix d A p
  let N : Matrix JetSlot JetSlot ℂ := fun k l => atlasOrderedJetEntry c A p k l
  have hN : Nᵀ = gradientEmbedding η * S * (gradientEmbedding η)ᴴ := by
    ext k l
    rw [Matrix.transpose_apply, gradient_factor_entry]
    change (η l.1 : ℂ) * (η k.1 : ℂ) * S k.2 l.2 = _
    rw [mul_comm (η l.1 : ℂ) (η k.1 : ℂ)]
  have hη : η' = T *ᵥ η := atlasChartUnitCovector_change c d p hc hd
  have hS : S' = tensorPairTransition T * S * (tensorPairTransition T)ᴴ :=
    atlasAmplitudeMatrix_change c d A p hc hd
  calc
    _ = (gradientEmbedding η' * S' * (gradientEmbedding η')ᴴ) j i := by
      rw [gradient_factor_entry]
      exact congrArg (fun t : ℂ => t * S' j.2 i.2) (mul_comm (η' i.1 : ℂ) (η' j.1 : ℂ))
    _ = (C * Nᵀ * Cᴴ) j i := by
      rw [hη, hS, hN]
      exact congrArg (fun Q : Matrix JetSlot JetSlot ℂ => Q j i)
        (jetCovariance_tensor_transition T η S).symm
    _ = _ := by simpa only [one_mul, N] using (orderedJet_congruence_entry C N 1 j i).symm

end Burnett.Microlocal.Overlap
