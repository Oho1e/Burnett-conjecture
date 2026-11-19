import Burnett.Geometry.Cotangent.Core
import Burnett.Counterexamples.RotatingNull.MeasureModel
import Burnett.Geometry.ManifoldVolumeRegularity

set_option autoImplicit false

noncomputable section

set_option autoImplicit false
noncomputable section

namespace Burnett.Bianchi.RayIdentification

open Bundle Set MeasureTheory Filter Bornology
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators ENNReal
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition UnitNullCompactness
open Burnett.RotatingNullMoments
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase)

def interval (τ : ℝ) : Set ℝ := Ioo (-τ) τ

/-- The open Lorentzian spacetime's underlying manifold is the actual open subtype. -/
def slab (τ : ℝ) : TopologicalSpace.Opens CoordinateSpace :=
  ⟨{x | x 0 ∈ interval τ}, isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous⟩

theorem slab_chart_apply {τ : ℝ} (c m : slab τ) : chartAt CoordinateSpace c m = (m : CoordinateSpace) :=
  rfl

theorem slab_chart_source {τ : ℝ} (c : slab τ) : (chartAt CoordinateSpace c).source = univ := by
  ext m
  simp [chartAt, TopologicalSpace.Opens.instChartedSpace]

theorem slab_chart_target {τ : ℝ} (c : slab τ) :
    (chartAt CoordinateSpace c).target = (slab τ : Set CoordinateSpace) := by
  rw [← (chartAt CoordinateSpace c).image_source_eq_target, slab_chart_source]
  change (Subtype.val : slab τ → CoordinateSpace) '' univ = _
  exact Subtype.coe_image_univ _

theorem slab_extChart_apply {τ : ℝ} (c m : slab τ) :
    extChartAt Model c m = (m : CoordinateSpace) := rfl

theorem slab_extChart_target {τ : ℝ} (c : slab τ) :
    (extChartAt Model c).target = (slab τ : Set CoordinateSpace) := by
  rw [extChartAt_target, slab_chart_target]
  simp [Model]

/-- The actual inverse tangent trivialization is the identity on this chart. -/
@[simp] theorem slab_symmL {τ : ℝ} (c m : slab τ) :
    (trivializationAt CoordinateSpace (TangentSpace Model) c).symmL ℝ m =
      (1 : CoordinateSpace →L[ℝ] CoordinateSpace) := by
  have hm : m ∈ (chartAt CoordinateSpace c).source := by rw [slab_chart_source]; trivial
  rw [TangentBundle.symmL_trivializationAt_eq_core hm, tangentBundleCore_coordChange_achart]
  have hEq : (extChartAt Model m ∘ (extChartAt Model c).symm) =ᶠ[𝓝 (m : CoordinateSpace)] id := by
    filter_upwards [(slab τ).isOpen.mem_nhds m.property] with y hy
    change extChartAt Model m ((extChartAt Model c).symm y) = y
    rw [slab_extChart_apply m, ← slab_extChart_apply c]
    exact (extChartAt Model c).right_inv (by rwa [slab_extChart_target])
  rw [slab_extChart_apply, hEq.fderivWithin_eq_of_nhds]
  simp [Model, fderivWithin_univ]
  rfl

theorem slab_tangentFrame {τ : ℝ} (c m : slab τ) (v : CoordinateSpace) :
    tangentFrame c m v = v := by
  rw [tangentFrame, slab_symmL]
  rfl


theorem slab_chart_transition_fderiv {τ : ℝ} (c d m : slab τ) :
    fderiv ℝ ((chartAt CoordinateSpace d) ∘ (chartAt CoordinateSpace c).symm)
      (chartAt CoordinateSpace c m) = (1 : CoordinateSpace →L[ℝ] CoordinateSpace) := by
  have heq : ((chartAt CoordinateSpace d) ∘ (chartAt CoordinateSpace c).symm) =ᶠ[𝓝 (m : CoordinateSpace)] id := by
    filter_upwards [(slab τ).isOpen.mem_nhds m.property] with y hy
    change chartAt CoordinateSpace d ((chartAt CoordinateSpace c).symm y) = y
    rw [slab_chart_apply d, ← slab_chart_apply c]
    exact (chartAt CoordinateSpace c).right_inv (by rwa [slab_chart_target])
  rw [slab_chart_apply, heq.fderiv_eq]
  exact fderiv_id

def slabEuclideanMetric (τ : ℝ) : ManifoldMetric.Metric (M := slab τ) where
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
      Trivialization.linearMapAt_apply, TangentSpace, slab_chart_source, slab_chart_transition_fderiv]

theorem slabEuclideanMetric_components (τ : ℝ) (c : slab τ) (x : CoordinateSpace) :
    metricComponents (coordinateMetric (slabEuclideanMetric τ) c) x = (1 : Matrix Index Index ℝ) := by
  ext i j
  change (slabEuclideanMetric τ).inner ((chartAt CoordinateSpace c).symm x)
    (tangentFrame c ((chartAt CoordinateSpace c).symm x) (coordinateBasis i))
    (tangentFrame c ((chartAt CoordinateSpace c).symm x) (coordinateBasis j)) = _
  rw [slab_tangentFrame, slab_tangentFrame]
  change ⟪coordinateBasis i, coordinateBasis j⟫_ℝ = _
  simp [coordinateBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, Matrix.one_apply]

/-- The actual Euclidean unit cotangent section of the slab. -/
def CotangentUnit (τ : ℝ) : Set (CotangentBundle (slab τ)) :=
  {p | dualEnergy (slabEuclideanMetric τ).inner
    (GlobalLeviCivita.inner_nondegenerate (slabEuclideanMetric τ)) p = 1}

theorem dualEnergy_slabEuclidean_coords {τ : ℝ} (c : slab τ) (p : CotangentBundle (slab τ)) :
    dualEnergy (slabEuclideanMetric τ).inner
      (GlobalLeviCivita.inner_nondegenerate (slabEuclideanMetric τ)) p =
        euclideanSquare (cotangentCoords c p) := by
  have hp : p.proj ∈ (chartAt CoordinateSpace c).source := by rw [slab_chart_source]; trivial
  have hcomp : metricComponents
      (coordinateBilinear (slabEuclideanMetric τ).inner c) (chartAt CoordinateSpace c p.proj) =
      (1 : Matrix Index Index ℝ) := slabEuclideanMetric_components τ c _
  rw [dualEnergy_chart _ _ (slabEuclideanMetric τ).symm c p hp, hcomp]
  unfold InverseField.matrixInverse
  rw [inv_one]
  unfold symbolNorm euclideanSquare
  simp [Matrix.one_apply, pow_two]

theorem cotangentUnit_iff {τ : ℝ} (c : slab τ) (p : CotangentBundle (slab τ)) :
    p ∈ CotangentUnit τ ↔ euclideanSquare (cotangentCoords c p) = 1 := by
  change dualEnergy _ _ p = 1 ↔ _
  rw [dualEnergy_slabEuclidean_coords c p]

end Burnett.Bianchi.RayIdentification

namespace Burnett.Bianchi.RayIdentification

open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators ENNReal
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition UnitNullCompactness
open Burnett.RotatingNullMoments
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase)

private theorem slab_chart_mem {τ : ℝ} (c m : slab τ) :
    m ∈ (chartAt CoordinateSpace c).source := by
  rw [slab_chart_source]
  exact mem_univ _

theorem continuous_slab_cotangentCoords {τ : ℝ} (c : slab τ) :
    Continuous (cotangentCoords c) := by
  have h := continuousOn_cotangentCoords c
  rw [slab_chart_source, preimage_univ] at h
  exact continuousOn_univ.mp h

theorem continuous_slab_cotangentAssemble {τ : ℝ} (c : slab τ) :
    Continuous (cotangentAssemble c) := by
  have h := continuousOn_cotangentAssemble c
  rw [slab_chart_source, preimage_univ] at h
  exact continuousOn_univ.mp h

/-- Cotangent phase coordinates use the actual Hom-bundle trivialization. -/
def cotangentChart {τ : ℝ} (c : slab τ) : CotangentBundle (slab τ) ≃ₜ slab τ × Covector where
  toFun p := (p.proj, cotangentCoords c p)
  invFun := cotangentAssemble c
  left_inv p := cotangentAssemble_coords c p (slab_chart_mem c p.proj)
  right_inv q := Prod.ext rfl (cotangentCoords_assemble c q (slab_chart_mem c q.1))
  continuous_toFun := continuous_cotangent_projection.prodMk (continuous_slab_cotangentCoords c)
  continuous_invFun := continuous_slab_cotangentAssemble c

theorem cotangentChart_apply {τ : ℝ} (c : slab τ) (p : CotangentBundle (slab τ)) :
    cotangentChart c p = (p.proj, cotangentCoords c p) := rfl

def toUnitPhase {τ : ℝ} (c : slab τ) (p : CotangentUnit τ) : UnitPhase (interval τ) :=
  ⟨((p.val.proj : CoordinateSpace), cotangentCoords c p.val),
    p.val.proj.property, (cotangentUnit_iff c p.val).mp p.property⟩

def unitPhasePoint {τ : ℝ} (p : UnitPhase (interval τ)) : slab τ :=
  ⟨p.val.1, p.property.1⟩

def fromUnitPhase {τ : ℝ} (c : slab τ) (p : UnitPhase (interval τ)) : CotangentUnit τ :=
  let q : slab τ × Covector := (unitPhasePoint p, p.val.2)
  ⟨cotangentAssemble c q, (cotangentUnit_iff c _).mpr <| by
    rw [cotangentCoords_assemble c q (slab_chart_mem c q.1)]
    exact p.property.2⟩

theorem toUnitPhase_val {τ : ℝ} (c : slab τ) (p : CotangentUnit τ) :
    (toUnitPhase c p).val = ((p.val.proj : CoordinateSpace), cotangentCoords c p.val) := rfl

theorem fromUnitPhase_projection {τ : ℝ} (c : slab τ) (p : UnitPhase (interval τ)) :
    (fromUnitPhase c p).val.proj = unitPhasePoint p := rfl

theorem fromUnitPhase_momenta {τ : ℝ} (c : slab τ) (p : UnitPhase (interval τ)) :
    cotangentCoords c (fromUnitPhase c p).val = p.val.2 :=
  cotangentCoords_assemble c (unitPhasePoint p, p.val.2) (slab_chart_mem c _)

/-- No antipodal identification: the genuine unit-dual bundle retains both orientations. -/
def unitPhaseHomeo {τ : ℝ} (c : slab τ) : CotangentUnit τ ≃ₜ UnitPhase (interval τ) where
  toFun := toUnitPhase c
  invFun := fromUnitPhase c
  left_inv p := Subtype.ext (cotangentAssemble_coords c p.val (slab_chart_mem c p.val.proj))
  right_inv p := Subtype.ext (Prod.ext rfl (fromUnitPhase_momenta c p))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_cotangent_projection).comp continuous_subtype_val).prodMk
      ((continuous_slab_cotangentCoords c).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hp : Continuous (unitPhasePoint (τ := τ)) := by
      apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val
    exact (continuous_slab_cotangentAssemble c).comp
      (hp.prodMk (continuous_snd.comp continuous_subtype_val))

instance instMeasurableSpaceCotangentUnit (τ : ℝ) : MeasurableSpace (CotangentUnit τ) := borel _
instance instBorelSpaceCotangentUnit (τ : ℝ) : BorelSpace (CotangentUnit τ) := ⟨rfl⟩

theorem isLocallyFiniteMeasure_map_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) (μ : Measure X) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.map e μ) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨s, hs, hOpen, hsmall⟩ := μ.exists_isOpen_measure_lt_top (e.symm y)
  refine ⟨e.symm ⁻¹' s, (hOpen.preimage e.symm.continuous).mem_nhds hs, ?_⟩
  rw [Measure.map_apply e.continuous.measurable (hOpen.preimage e.symm.continuous).measurableSet]
  have he : e ⁻¹' (e.symm ⁻¹' s) = s := by
    ext x
    simp
  rwa [he]

def coordinateUnitMeasure {τ : ℝ} (c : slab τ) (μ : Measure (CotangentUnit τ)) :
    Measure (UnitPhase (interval τ)) :=
  Measure.map (unitPhaseHomeo c) μ

theorem coordinateUnitMeasure_locallyFinite {τ : ℝ} (c : slab τ)
    (μ : Measure (CotangentUnit τ)) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (coordinateUnitMeasure c μ) :=
  isLocallyFiniteMeasure_map_homeomorph (unitPhaseHomeo c) μ

theorem coordinateUnitMeasure_integral {τ : ℝ} (c : slab τ)
    (μ : Measure (CotangentUnit τ)) (f : UnitPhase (interval τ) → ℝ) :
    (∫ q, f q ∂coordinateUnitMeasure c μ) = ∫ p, f (toUnitPhase c p) ∂μ :=
  (unitPhaseHomeo c).toMeasurableEquiv.measurableEmbedding.integral_map f

theorem coordinateUnitMeasure_integrable_iff {τ : ℝ} (c : slab τ)
    (μ : Measure (CotangentUnit τ)) (f : UnitPhase (interval τ) → ℝ) :
    Integrable f (coordinateUnitMeasure c μ) ↔ Integrable (fun p => f (toUnitPhase c p)) μ :=
  (unitPhaseHomeo c).toMeasurableEquiv.measurableEmbedding.integrable_map_iff

theorem coordinateUnitMeasure_ae_iff {τ : ℝ} (c : slab τ)
    (μ : Measure (CotangentUnit τ)) (P : UnitPhase (interval τ) → Prop) :
    (∀ᵐ q ∂coordinateUnitMeasure c μ, P q) ↔ ∀ᵐ p ∂μ, P (toUnitPhase c p) :=
  (unitPhaseHomeo c).toMeasurableEquiv.measurableEmbedding.ae_map_iff

end Burnett.Bianchi.RayIdentification

namespace Burnett.Bianchi.RayIdentification

open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition UnitNullCompactness

abbrev Phase := CoordinateSpace × Covector

def slabPhaseDomain (τ : ℝ) : Set Phase :=
  {q | q.1 ∈ (slab τ : Set CoordinateSpace) ∧ q.2 ≠ 0}

/-- Use the actual preferred cotangent trivialization over the base-chart inverse. -/
def assemblePhase {τ : ℝ} (c : slab τ) (q : Phase) : CotangentBundle (slab τ) :=
  cotangentAssemble c ((chartAt CoordinateSpace c).symm q.1, q.2)

theorem assemblePhase_projection {τ : ℝ} (c : slab τ) (q : Phase)
    (hq : q.1 ∈ (slab τ : Set CoordinateSpace)) :
    ((assemblePhase c q).proj : CoordinateSpace) = q.1 := by
  have ht : q.1 ∈ (chartAt CoordinateSpace c).target := by rw [slab_chart_target]; exact hq
  change (((chartAt CoordinateSpace c).symm q.1 : slab τ) : CoordinateSpace) = q.1
  exact (chartAt CoordinateSpace c).right_inv ht

theorem assemblePhase_coords {τ : ℝ} (c d : slab τ) (q : Phase) :
    cotangentCoords c (assemblePhase d q) = q.2 := by
  have he (p : CotangentBundle (slab τ)) : cotangentCoords c p = cotangentCoords d p := by
    funext i
    simp only [cotangentCoords, cotangentTrivialization_apply, slab_tangentFrame]
  rw [he]
  exact cotangentCoords_assemble d ((chartAt CoordinateSpace d).symm q.1, q.2)
    (slab_chart_mem d _)

def pullbackTest {τ : ℝ} (c : slab τ) (a : CoordinateSpace → Covector → ℝ)
    (p : CotangentBundle (slab τ)) : ℝ :=
  a (p.proj : CoordinateSpace) (cotangentCoords c p)

/-- Chartwise smooth test on the genuine punctured cotangent bundle. -/
def IntrinsicTransportTest (τ : ℝ) (a : CotangentBundle (slab τ) → ℝ) : Prop :=
  (∀ c : slab τ, ContDiffOn ℝ ∞ (a ∘ assemblePhase c) (slabPhaseDomain τ)) ∧
  (∀ (p : CotangentBundle (slab τ)) (t : ℝ), p.2 ≠ 0 → 0 < t →
    a (cotangentScale t p) = t * a p) ∧
  ∃ K : Set (slab τ), IsCompact K ∧
    ∀ p : CotangentBundle (slab τ), p.proj ∉ K → p.2 ≠ 0 → a p = 0

theorem cotangentCoords_ne_zero_iff {τ : ℝ} (c : slab τ) (p : CotangentBundle (slab τ)) :
    cotangentCoords c p ≠ 0 ↔ p.2 ≠ 0 := by
  constructor
  · intro hc h
    apply hc
    funext i
    simp [cotangentCoords, cotangentTrivialization_apply, h]
  · intro hp h
    apply hp
    have he (i : Index) : p.2 (coordinateBasis i) = 0 := by
      have hi := congrFun h i
      simpa only [cotangentCoords, cotangentTrivialization_apply, slab_tangentFrame,
        Pi.zero_apply] using hi
    have hz : p.2.toLinearMap = 0 := by
      apply coordinateBasis.ext
      intro i
      exact he i
    ext v
    exact congrArg (fun f : CoordinateSpace →ₗ[ℝ] ℝ => f v) hz

theorem pullbackTest_intrinsic {τ : ℝ} (c : slab τ) (a : CoordinateSpace → Covector → ℝ)
    (hSmooth : ContDiffOn ℝ ∞ (fun q : Phase => a q.1 q.2) (slabPhaseDomain τ))
    (hScale : ∀ x ∈ (slab τ : Set CoordinateSpace), ∀ ξ : Covector, ξ ≠ 0 →
      ∀ t : ℝ, 0 < t → a x (t • ξ) = t * a x ξ)
    (hCompact : ∃ K : Set CoordinateSpace, IsCompact K ∧ K ⊆ (slab τ : Set CoordinateSpace) ∧
      ∀ x ∉ K, ∀ ξ : Covector, ξ ≠ 0 → a x ξ = 0) :
    IntrinsicTransportTest τ (pullbackTest c a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    apply hSmooth.congr
    intro q hq
    simp only [Function.comp_apply, pullbackTest, assemblePhase_projection d q hq.1, assemblePhase_coords]
  · intro p t hp ht
    simp only [pullbackTest, cotangentScale_projection, cotangentScale_coords]
    exact hScale _ p.proj.property _ ((cotangentCoords_ne_zero_iff c p).mpr hp) t ht
  · obtain ⟨K, hK, hsub, hzero⟩ := hCompact
    let L : Set (slab τ) := Subtype.val ⁻¹' K
    have hL : IsCompact L := by
      rw [Subtype.isCompact_iff]
      convert hK using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    exact ⟨L, hL, fun p hp hξ => hzero (p.proj : CoordinateSpace) hp _
      ((cotangentCoords_ne_zero_iff c p).mpr hξ)⟩

/-- Actual intrinsic determinant volume on the slab has the corresponding restricted coordinate density. -/
theorem map_geometricMeasure_of_slab_components {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ)) (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x) :
    Measure.map (Subtype.val : slab τ → CoordinateSpace) (ManifoldVolume.geometricMeasure g) =
      (LorentzVolume.coordinateMeasure G).restrict (slab τ : Set CoordinateSpace) := by
  have h := ManifoldVolume.map_chart_geometricMeasure g c
  rw [slab_chart_source, Measure.restrict_univ, slab_chart_target] at h
  change Measure.map (Subtype.val : slab τ → CoordinateSpace) (ManifoldVolume.geometricMeasure g) =
    _ at h
  rw [h, ManifoldVolume.coordinateMeasure, LorentzVolume.coordinateMeasure,
    LorentzVolume.coordinateMeasure, restrict_withDensity (slab τ).isOpen.measurableSet,
    restrict_withDensity (slab τ).isOpen.measurableSet]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (slab τ).isOpen.measurableSet] with x hx
  unfold LorentzVolume.density
  rw [hG x hx]

end Burnett.Bianchi.RayIdentification

namespace Burnett.Bianchi.RayIdentification

open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition UnitNullCompactness
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)

/-- The Hamiltonian on the actual continuous-dual bundle. -/
def intrinsicHamiltonian {τ : ℝ} (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (p : CotangentBundle (slab τ)) : ℝ :=
  dualEnergy g hgn p / 2

def coordinateHamiltonian (G : CoordinateSpace → Tensor2) (x : CoordinateSpace) (ξ : Covector) : ℝ :=
  symbolNorm (InverseField.matrixInverse (G x)) ξ / 2

theorem intrinsicHamiltonian_assemble {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (x : CoordinateSpace) (hx : x ∈ (slab τ : Set CoordinateSpace)) (ξ : Covector) :
    intrinsicHamiltonian g hgn (assemblePhase c (x, ξ)) = coordinateHamiltonian G x ξ := by
  have hproj : chartAt CoordinateSpace c (assemblePhase c (x, ξ)).proj = x :=
    (slab_chart_apply c _).trans (assemblePhase_projection c (x, ξ) hx)
  rw [intrinsicHamiltonian, dualEnergy_chart g hgn hs c _ (slab_chart_mem c _),
    hproj, assemblePhase_coords, hG x hx]
  rfl

theorem intrinsicHamiltonian_eq_coordinates {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (p : CotangentBundle (slab τ)) :
    intrinsicHamiltonian g hgn p =
      coordinateHamiltonian G (p.proj : CoordinateSpace) (cotangentCoords c p) := by
  rw [intrinsicHamiltonian, dualEnergy_chart g hgn hs c p (slab_chart_mem c _),
    slab_chart_apply, hG _ p.proj.property]
  rfl

/-- Actual Poisson differentiation in the canonical base and fiber coordinates. -/
def canonicalBracket (P a : CoordinateSpace → Covector → ℝ)
    (x : CoordinateSpace) (ξ : Covector) : ℝ :=
  ∑ i, (momentumPartial i P x ξ * basePartial i a x ξ -
    basePartial i P x ξ * momentumPartial i a x ξ)

theorem canonicalBracket_congr {P P' a a' : CoordinateSpace → Covector → ℝ}
    (x : CoordinateSpace) (ξ : Covector)
    (hbP : (fun y => P y ξ) =ᶠ[𝓝 x] (fun y => P' y ξ))
    (hba : (fun y => a y ξ) =ᶠ[𝓝 x] (fun y => a' y ξ))
    (hfP : P x = P' x) (hfa : a x = a' x) :
    canonicalBracket P a x ξ = canonicalBracket P' a' x ξ := by
  simp only [canonicalBracket, basePartial, momentumPartial, hfP, hfa, hbP.fderiv_eq, hba.fderiv_eq]

/-- The Hamilton derivative is computed before restriction to the unit bundle. -/
def intrinsicHamiltonDerivative {τ : ℝ} (c : slab τ) (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (a : CotangentBundle (slab τ) → ℝ)
    (p : CotangentBundle (slab τ)) : ℝ :=
  canonicalBracket
    (fun x ξ => intrinsicHamiltonian g hgn (assemblePhase c (x, ξ)))
    (fun x ξ => a (assemblePhase c (x, ξ))) (p.proj : CoordinateSpace) (cotangentCoords c p)

theorem intrinsicHamiltonDerivative_pullback {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (a : CoordinateSpace → Covector → ℝ) (p : CotangentBundle (slab τ)) :
    intrinsicHamiltonDerivative c g hgn (pullbackTest c a) p =
      canonicalBracket (coordinateHamiltonian G) a (p.proj : CoordinateSpace) (cotangentCoords c p) := by
  unfold intrinsicHamiltonDerivative
  apply canonicalBracket_congr
  · filter_upwards [(slab τ).isOpen.mem_nhds p.proj.property] with y hy
    exact intrinsicHamiltonian_assemble c g hgn hs G hG y hy _
  · filter_upwards [(slab τ).isOpen.mem_nhds p.proj.property] with y hy
    simp only [pullbackTest, assemblePhase_projection c (y, cotangentCoords c p) hy,
      assemblePhase_coords]
  · funext ξ
    exact intrinsicHamiltonian_assemble c g hgn hs G hG _ p.proj.property ξ
  · funext ξ
    simp only [pullbackTest, assemblePhase_projection c ((p.proj : CoordinateSpace), ξ) p.proj.property,
      assemblePhase_coords]

theorem coordinateUnitMeasure_intrinsicTransport {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (μ : Measure (CotangentUnit τ))
    (htransport : ∀ b, IntrinsicTransportTest τ b →
      ∫ p : CotangentUnit τ, intrinsicHamiltonDerivative c g hgn b p.val ∂μ = 0)
    (a : CoordinateSpace → Covector → ℝ)
    (ha : IntrinsicTransportTest τ (pullbackTest c a)) :
    (∫ q : Burnett.RotatingNullMoments.MeasureModel.UnitPhase (interval τ),
      canonicalBracket (coordinateHamiltonian G) a q.val.1 q.val.2 ∂coordinateUnitMeasure c μ) = 0 := by
  rw [coordinateUnitMeasure_integral]
  simpa only [toUnitPhase_val, intrinsicHamiltonDerivative_pullback c g hgn hs G hG] using
    htransport (pullbackTest c a) ha

theorem coordinateUnitMeasure_intrinsicNull {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (G : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (μ : Measure (CotangentUnit τ))
    (hn : ∀ᵐ p : CotangentUnit τ ∂μ, intrinsicHamiltonian g hgn p.val = 0) :
    ∀ᵐ q : Burnett.RotatingNullMoments.MeasureModel.UnitPhase (interval τ) ∂coordinateUnitMeasure c μ,
      coordinateHamiltonian G q.val.1 q.val.2 = 0 := by
  apply (coordinateUnitMeasure_ae_iff c μ _).mpr
  filter_upwards [hn] with p hp
  simpa only [toUnitPhase_val, intrinsicHamiltonian_eq_coordinates c g hgn hs G hG] using hp

end Burnett.Bianchi.RayIdentification

namespace Burnett.Bianchi.RayIdentification

open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition UnitNullCompactness
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase IsTensorTest phaseContraction)

abbrev ContravariantField (τ : ℝ) :=
  slab τ → CotangentModel →ₗ[ℝ] CotangentModel →ₗ[ℝ] ℝ

def evalCovector {τ : ℝ} (c m : slab τ) (i : Index) :
    CotangentModel →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ : CoordinateSpace →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (tangentFrame c m (coordinateBasis i))

def tensorInSlab {τ : ℝ} (c : slab τ) (S : CoordinateSpace → Tensor2) : ContravariantField τ :=
  fun m => ∑ i : Index, ∑ j : Index,
    S (m : CoordinateSpace) i j • (evalCovector c m i).toLinearMap.smulRight ((evalCovector c m j).toLinearMap)

theorem tensorInSlab_apply {τ : ℝ} (c : slab τ) (S : CoordinateSpace → Tensor2) (m : slab τ)
    (ξ η : CotangentFiber m) :
    tensorInSlab c S m ξ η =
      ∑ i, ∑ j, S (m : CoordinateSpace) i j * evalCovector c m i ξ * evalCovector c m j η := by
  simp [tensorInSlab, LinearMap.sum_apply, mul_comm, mul_left_comm]

def tensorTestComponents {τ : ℝ} (c : slab τ) (T : ContravariantField τ) (m : slab τ) : Tensor2 :=
  fun i j => T m (cotangentAssemble c (m, Pi.single i 1)).2
    (cotangentAssemble c (m, Pi.single j 1)).2

theorem evalCovector_assemble {τ : ℝ} (c d m : slab τ) (ξ : Covector) (i : Index) :
    evalCovector c m i (cotangentAssemble d (m, ξ)).2 = ξ i := by
  have h := congrFun (cotangentCoords_assemble d (m, ξ) (slab_chart_mem d m)) i
  simpa [evalCovector, cotangentCoords, cotangentTrivialization_apply, slab_tangentFrame] using h

theorem tensorTestComponents_inSlab {τ : ℝ} (c d : slab τ)
    (S : CoordinateSpace → Tensor2) (m : slab τ) :
    tensorTestComponents d (tensorInSlab c S) m = S (m : CoordinateSpace) := by
  funext i j
  rw [tensorTestComponents, tensorInSlab_apply]
  simp [evalCovector_assemble, Pi.single_apply]

def IntrinsicTensorTest (τ : ℝ) (T : ContravariantField τ) : Prop :=
  (∀ c : slab τ, ContDiffOn ℝ ∞ (fun x : CoordinateSpace =>
    tensorTestComponents c T ((chartAt CoordinateSpace c).symm x)) (slab τ : Set CoordinateSpace)) ∧
  (∃ K : Set (slab τ), IsCompact K ∧ ∀ m ∉ K, T m = 0) ∧
  ∀ m ξ η, T m ξ η = T m η ξ

theorem tensorInSlab_intrinsic {τ : ℝ} (c : slab τ) (S : CoordinateSpace → Tensor2)
    (hS : IsTensorTest (interval τ) S) : IntrinsicTensorTest τ (tensorInSlab c S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    apply hS.1.contDiffOn.congr
    intro x hx
    rw [tensorTestComponents_inSlab, ← slab_chart_apply d]
    exact congrArg S ((chartAt CoordinateSpace d).right_inv (by rwa [slab_chart_target]))
  · let K : Set (slab τ) := Subtype.val ⁻¹' tsupport S
    have hKset : Subtype.val '' K = tsupport S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hS.2.2.1 hx⟩, hx, rfl⟩
    have hK : IsCompact K := by
      rw [Subtype.isCompact_iff, hKset]
      exact hS.2.1
    refine ⟨K, hK, fun m hm => ?_⟩
    have hz : S (m : CoordinateSpace) = 0 := image_eq_zero_of_notMem_tsupport hm
    rw [tensorInSlab]
    simp [hz]
  · intro m ξ η
    rw [tensorInSlab_apply, tensorInSlab_apply, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hS.2.2.2 _ i j]
    ring

theorem tensorInSlab_phaseContraction {τ : ℝ} (c : slab τ) (S : CoordinateSpace → Tensor2)
    (p : CotangentUnit τ) :
    tensorInSlab c S p.val.proj p.val.2 p.val.2 =
      phaseContraction (interval τ) S (toUnitPhase c p) := by
  rw [tensorInSlab_apply]
  unfold phaseContraction
  simp only [toUnitPhase_val, evalCovector, ContinuousLinearMap.apply_apply,
    cotangentCoords, cotangentTrivialization_apply]
  rfl

def covariantTensorComponents {τ : ℝ} (c : slab τ)
    (Ein : (m : slab τ) → LinearMap.BilinForm ℝ (TangentSpace Model m)) (m : slab τ) : Tensor2 :=
  fun i j => Ein m (tangentFrame c m (coordinateBasis i)) (tangentFrame c m (coordinateBasis j))

def HasIntrinsicTensorMoments {τ : ℝ} (c : slab τ) (g : ManifoldBilinear.Field (M := slab τ))
    (Ein : (m : slab τ) → LinearMap.BilinForm ℝ (TangentSpace Model m))
    (μ : Measure (CotangentUnit τ)) : Prop :=
  ∀ T : ContravariantField τ, IntrinsicTensorTest τ T →
    (∫ p : CotangentUnit τ, T p.val.proj p.val.2 p.val.2 ∂μ) =
      ∫ x : slab τ, (∑ i, ∑ j, covariantTensorComponents c Ein x i j * tensorTestComponents c T x i j)
        ∂ManifoldVolume.geometricMeasure g

/-- Actual cotangent contractions pull forward to the coordinate moment identities. -/
theorem coordinateUnitMeasure_intrinsicMoments {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ)) (G E : CoordinateSpace → Tensor2)
    (hG : ∀ x ∈ (slab τ : Set CoordinateSpace), metricComponents (coordinateBilinear g c) x = G x)
    (μ : Measure (CotangentUnit τ))
    (Ein : (m : slab τ) → LinearMap.BilinForm ℝ (TangentSpace Model m))
    (hEin : ∀ x : slab τ, covariantTensorComponents c Ein x = E (x : CoordinateSpace))
    (hmom : HasIntrinsicTensorMoments c g Ein μ)
    (S : CoordinateSpace → Tensor2) (hS : IsTensorTest (interval τ) S) :
    (∫ p, phaseContraction (interval τ) S p ∂coordinateUnitMeasure c μ) =
      ∫ x, (∑ i, ∑ j, E x i j * S x i j) ∂(LorentzVolume.coordinateMeasure G).restrict (slab τ : Set CoordinateSpace) := by
  rw [coordinateUnitMeasure_integral, ← map_geometricMeasure_of_slab_components c g G hG]
  have he : MeasurableEmbedding (Subtype.val : slab τ → CoordinateSpace) :=
    MeasurableEmbedding.subtype_coe (slab τ).isOpen.measurableSet
  rw [he.integral_map]
  simpa only [tensorInSlab_phaseContraction, tensorTestComponents_inSlab, hEin] using
    hmom (tensorInSlab c S) (tensorInSlab_intrinsic c S hS)

end Burnett.Bianchi.RayIdentification

namespace Burnett.Bianchi.RayIdentification

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric UnitNullCompactness
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)

/-- A homogeneous identity on an open base patch differentiates at every base point. -/
theorem basePartial_radial (U : Set CoordinateSpace) (hU : IsOpen U)
    (f : CoordinateSpace → Covector → ℝ) (i : Index) (x : CoordinateSpace)
    (hx : x ∈ U) (ξ : Covector) (t w : ℝ)
    (h : ∀ y ∈ U, f y (t • ξ) = w * f y ξ) :
    basePartial i f x (t • ξ) = w * basePartial i f x ξ := by
  have he : (fun y => f y (t • ξ)) =ᶠ[𝓝 x] (w • (fun y => f y ξ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact h y hy
  simp only [basePartial, he.fderiv_eq, fderiv_const_smul_of_field, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- A homogeneous identity differentiates along the true punctured fiber. -/
theorem smul_momentumPartial_radial (f : CoordinateSpace → Covector → ℝ)
    (i : Index) (x : CoordinateSpace) (ξ : Covector) (hξ : ξ ≠ 0) (t w : ℝ)
    (h : ∀ η : Covector, η ≠ 0 → f x (t • η) = w * f x η) :
    t * momentumPartial i f x (t • ξ) = w * momentumPartial i f x ξ := by
  have hn : {η : Covector | η ≠ 0} ∈ 𝓝 ξ :=
    isOpen_ne.mem_nhds hξ
  have he : (fun η => f x (t • η)) =ᶠ[𝓝 ξ] (w • f x) := by
    filter_upwards [hn] with η hη
    exact h η hη
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_smul, fderiv_const_smul_of_field] at hd
  simpa only [momentumPartial, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun D : Covector →L[ℝ] ℝ => D (Burnett.RotatingNullMoments.CanonicalHamilton.momentumBasis i)) hd

theorem canonicalBracket_radial (U : Set CoordinateSpace) (hU : IsOpen U)
    (P a : CoordinateSpace → Covector → ℝ) (x : CoordinateSpace)
    (hx : x ∈ U) (ξ : Covector) (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t)
    (hP : ∀ y ∈ U, ∀ η ≠ (0 : Covector), P y (t • η) = t^2 * P y η)
    (ha : ∀ y ∈ U, ∀ η ≠ (0 : Covector), a y (t • η) = t * a y η) :
    canonicalBracket P a x (t • ξ) = t^2 * canonicalBracket P a x ξ := by
  have hmP (i : Index) : momentumPartial i P x (t • ξ) = t * momentumPartial i P x ξ := by
    apply mul_left_cancel₀ ht.ne'
    calc
      t * momentumPartial i P x (t • ξ) = t^2 * momentumPartial i P x ξ :=
        smul_momentumPartial_radial P i x ξ hξ t (t^2) (hP x hx)
      _ = t * (t * momentumPartial i P x ξ) := by ring
  have hma (i : Index) : momentumPartial i a x (t • ξ) = momentumPartial i a x ξ :=
    mul_left_cancel₀ ht.ne' (smul_momentumPartial_radial a i x ξ hξ t t (ha x hx))
  unfold canonicalBracket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hmP, hma, basePartial_radial U hU P i x hx ξ t (t^2) (fun y hy => hP y hy ξ hξ),
    basePartial_radial U hU a i x hx ξ t t (fun y hy => ha y hy ξ hξ)]
  ring

theorem assemblePhase_scale {τ : ℝ} (c : slab τ)
    (x : CoordinateSpace) (ξ : Covector) (t : ℝ) :
    assemblePhase c (x, t • ξ) = cotangentScale t (assemblePhase c (x, ξ)) := by
  have he := cotangentAssemble_coords c (cotangentScale t (assemblePhase c (x, ξ)))
    (slab_chart_mem c _)
  rw [cotangentScale_projection, cotangentScale_coords, assemblePhase_coords] at he
  exact he

theorem intrinsicHamiltonian_scale {τ : ℝ} (g : ManifoldBilinear.Field (M := slab τ))
    (hgn : ManifoldBilinear.IsNondegenerate g) (t : ℝ) (p : CotangentBundle (slab τ)) :
    intrinsicHamiltonian g hgn (cotangentScale t p) = t^2 * intrinsicHamiltonian g hgn p := by
  rw [intrinsicHamiltonian, dualEnergy_cotangentScale, intrinsicHamiltonian]
  ring

/-- The pre-restriction Hamilton derivative of an admissible test has degree two. -/
theorem intrinsicHamiltonDerivative_scale {τ : ℝ} (c : slab τ)
    (g : ManifoldBilinear.Field (M := slab τ)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (a : CotangentBundle (slab τ) → ℝ) (ha : IntrinsicTransportTest τ a)
    (p : CotangentBundle (slab τ)) (hp : p.2 ≠ 0) (t : ℝ) (ht : 0 < t) :
    intrinsicHamiltonDerivative c g hgn a (cotangentScale t p) =
      t^2 * intrinsicHamiltonDerivative c g hgn a p := by
  simp only [intrinsicHamiltonDerivative, cotangentScale_projection, cotangentScale_coords]
  apply canonicalBracket_radial ((slab τ : Set CoordinateSpace)) (slab τ).isOpen
    _ _ _ p.proj.property _ ((cotangentCoords_ne_zero_iff c p).2 hp) t ht
  · intro y _ η _
    rw [assemblePhase_scale, intrinsicHamiltonian_scale]
  · intro y _ η hη
    rw [assemblePhase_scale]
    apply ha.2.1 _ t _ ht
    apply (cotangentCoords_ne_zero_iff c (assemblePhase c (y, η))).1
    rwa [assemblePhase_coords]

theorem tensorContraction_scale {τ : ℝ} (T : ContravariantField τ)
    (p : CotangentBundle (slab τ)) (t : ℝ) :
    T (cotangentScale t p).proj (cotangentScale t p).2 (cotangentScale t p).2 =
      t^2 * T p.proj p.2 p.2 := by
  change T p.proj (t • p.2) (t • p.2) = t^2 * T p.proj p.2 p.2
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end Burnett.Bianchi.RayIdentification
