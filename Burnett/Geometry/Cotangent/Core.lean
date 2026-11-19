import Burnett.Geometry.GlobalLeviCivita
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Geometry.GramCoordinateBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitNullCompactness

open Matrix Set
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.GramCoordinateBound
open Burnett.Geometry.InverseField (matrixInverse)
open scoped BigOperators

variable {B : Type*} [TopologicalSpace B]

theorem symbolNorm_eq_gramEnergy (A : Matrix Index Index ℝ) (ξ : Covector) :
    symbolNorm A ξ = gramEnergy A ξ := by
  unfold symbolNorm gramEnergy
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem continuousOn_symbolNorm (G : B → Tensor2) {K : Set B} (hG : ContinuousOn G K) :
    ContinuousOn (fun p : B × Covector => symbolNorm (G p.1) p.2) (Prod.fst ⁻¹' K) := by
  have h1 : ContinuousOn (fun p : B × Covector => G p.1) (Prod.fst ⁻¹' K) :=
    hG.comp continuous_fst.continuousOn (fun _ hp => hp)
  have hg (i j : Index) : ContinuousOn (fun p : B × Covector => G p.1 i j) (Prod.fst ⁻¹' K) :=
    continuousOn_pi.mp (continuousOn_pi.mp h1 i) j
  have hv (i : Index) : Continuous (fun p : B × Covector => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  unfold symbolNorm
  exact continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
    ((hg i j).mul (hv i).continuousOn).mul (hv j).continuousOn

/-- A uniform lower metric bound written as control of the coordinate norm. -/
theorem exists_inverseGram_coordinate_bound (R : B → Tensor2) {K : Set B}
    (hK : IsCompact K) (hR : ContinuousOn R K) (hP : ∀ x ∈ K, Matrix.PosDef (R x)) :
    ∃ C > (0 : ℝ), ∀ x ∈ K, ∀ ξ : Covector,
      ‖ξ‖ ≤ C * gramNorm (matrixInverse (R x)) ξ := by
  have hd (i : Index) : ContinuousOn (fun x => R x i i) K :=
    continuousOn_pi.mp (continuousOn_pi.mp hR i) i
  have hbound (i : Index) : ∃ D > (0 : ℝ), ∀ y ∈ (fun x => R x i i) '' K, ‖y‖ ≤ D :=
    ((hK.image_of_continuousOn (hd i)).isBounded).exists_pos_norm_le
  choose D hD hb using hbound
  let C : ℝ := 1 + ∑ i, Real.sqrt (D i)
  have hC : 0 < C := by
    unfold C
    have hh : 0 ≤ ∑ i, Real.sqrt (D i) := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg (D i)
    linarith
  refine ⟨C, hC, fun x hx ξ => (pi_norm_le_iff_of_nonneg
    (mul_nonneg hC.le (gramNorm_nonneg _ _))).mpr ?_⟩
  intro i
  let A : Matrix Index Index ℝ := R x
  have hA : A.PosDef := hP x hx
  have hD' : A i i ≤ D i := by
    have hu := hb i (R x i i) (mem_image_of_mem _ hx)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hu)
  have hAi : A⁻¹⁻¹ = A :=
    Matrix.nonsing_inv_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hp := norm_apply_le_sqrt_inverse_diagonal_mul_gramNorm A⁻¹ hA.inv ξ i
  rw [hAi] at hp
  change ‖ξ i‖ ≤ C * gramNorm A⁻¹ ξ
  have hr : Real.sqrt (D i) ≤ C := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Real.sqrt_nonneg (D j))
      (Finset.mem_univ i)
    unfold C
    linarith
  exact hp.trans (mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_sqrt hD').trans hr) (gramNorm_nonneg _ _))

/-- An actual auxiliary unit section intersected with the Lorentz null cone. -/
def unitNull (R G : B → Tensor2) : Set (B × Covector) :=
  {p | symbolNorm (matrixInverse (R p.1)) p.2 = 1 ∧
       symbolNorm (matrixInverse (G p.1)) p.2 = 0}

omit [TopologicalSpace B] in
theorem unitNull_covector_ne_zero {R G : B → Tensor2} {p : B × Covector} (hp : p ∈ unitNull R G) :
    p.2 ≠ 0 := by
  intro h
  have h1 := hp.1
  rw [h] at h1
  simp [symbolNorm] at h1

private theorem isCompact_fiber_level_of_bounded {f : B × Covector → ℝ × ℝ} {K : Set B}
    (hK : IsCompact K) (hf : ContinuousOn f (Prod.fst ⁻¹' K)) (C : ℝ)
    (hb : ∀ p : B × Covector, f p = (1, 0) → p.1 ∈ K → ‖p.2‖ ≤ C) :
    IsCompact {p : B × Covector | f p = (1, 0) ∧ p.1 ∈ K} := by
  obtain ⟨D, hD, hDE⟩ := continuousOn_iff_isClosed.mp hf ({(1, 0)} : Set (ℝ × ℝ)) isClosed_singleton
  have hre : {p : B × Covector | f p = (1, 0) ∧ p.1 ∈ K} = (K ×ˢ Metric.closedBall 0 C) ∩ D := by
    ext p
    constructor
    · rintro ⟨hp, hk⟩
      have hlev : p ∈ f ⁻¹' {(1, 0)} ∩ Prod.fst ⁻¹' K := ⟨hp, hk⟩
      rw [hDE] at hlev
      exact ⟨⟨hk, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb p hp hk⟩, hlev.1⟩
    · rintro ⟨⟨hk, _⟩, hpD⟩
      have hlev : p ∈ D ∩ Prod.fst ⁻¹' K := ⟨hpD, hk⟩
      rw [← hDE] at hlev
      exact ⟨hlev.1, hk⟩
  rw [hre]
  exact (hK.prod (isCompact_closedBall _ _)).inter_right hD

theorem isCompact_unitNull_over (R G : B → Tensor2) {K : Set B}
    (hK : IsCompact K) (hR : ContinuousOn R K) (hG : ContinuousOn G K)
    (hRpos : ∀ x ∈ K, Matrix.PosDef (R x)) (hGdet : ∀ x ∈ K, Matrix.det (G x) ≠ 0) :
    IsCompact {p ∈ unitNull R G | p.1 ∈ K} := by
  obtain ⟨C, _, hb⟩ := exists_inverseGram_coordinate_bound R hK hR hRpos
  let f : B × Covector → ℝ × ℝ := fun p =>
    (symbolNorm (matrixInverse (R p.1)) p.2, symbolNorm (matrixInverse (G p.1)) p.2)
  have hRinv : ContinuousOn (fun x => matrixInverse (R x)) K :=
    InverseField.continuousOn_matrixInverse R K hR (fun x hx => (hRpos x hx).det_pos.ne')
  have hGinv : ContinuousOn (fun x => matrixInverse (G x)) K :=
    InverseField.continuousOn_matrixInverse G K hG hGdet
  have hf : ContinuousOn f (Prod.fst ⁻¹' K) :=
    (continuousOn_symbolNorm (fun x => matrixInverse (R x)) (K := K) hRinv).prodMk
      (continuousOn_symbolNorm (fun x => matrixInverse (G x)) (K := K) hGinv)
  have hr : {p ∈ unitNull R G | p.1 ∈ K} =
      {p : B × Covector | f p = (1, 0) ∧ p.1 ∈ K} := by
    ext p
    simp only [unitNull, f, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hr]
  apply isCompact_fiber_level_of_bounded hK hf C
  intro p hp hk
  have hR' : symbolNorm (matrixInverse (R p.1)) p.2 = 1 := congrArg Prod.fst hp
  have hg : gramNorm (matrixInverse (R p.1)) p.2 = 1 := by
    unfold gramNorm
    rw [← symbolNorm_eq_gramEnergy, hR', Real.sqrt_one]
  simpa only [hg, mul_one] using hb p.1 hk p.2

/-- The same compact preimage on the actual unit-null subtype. -/
theorem isCompact_unitNullSubtype_preimage (R G : B → Tensor2) {K : Set B}
    (hK : IsCompact K) (hR : ContinuousOn R K) (hG : ContinuousOn G K)
    (hRpos : ∀ x ∈ K, Matrix.PosDef (R x)) (hGdet : ∀ x ∈ K, Matrix.det (G x) ≠ 0) :
    IsCompact {ω : unitNull R G | (ω : B × Covector).1 ∈ K} := by
  rw [Subtype.isCompact_iff]
  have hEq : Subtype.val '' {ω : unitNull R G | (ω : B × Covector).1 ∈ K} =
      {p ∈ unitNull R G | p.1 ∈ K} := by
    ext p
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω.property, hω⟩
    · rintro ⟨hω, hk⟩
      exact ⟨⟨p, hω⟩, hk, rfl⟩
  rw [hEq]
  exact isCompact_unitNull_over R G hK hR hG hRpos hGdet

end Burnett.Geometry.UnitNullCompactness

namespace Burnett.Geometry.UnitNullCompactness

open Matrix Set Bundle LinearMap
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField (matrixInverse)
open scoped Manifold ContDiff BigOperators
open ManifoldMetric ManifoldMetricTransition

def inverseQuadratic {B : Type*} (G : B → Tensor2) (x : B) : LinearMap.BilinForm ℝ Covector :=
  Matrix.toBilin (Pi.basisFun ℝ Index) (matrixInverse (G x))

theorem inverseQuadratic_self {B : Type*} (G : B → Tensor2) (x : B) (ξ : Covector) :
    inverseQuadratic G x ξ ξ = symbolNorm (matrixInverse (G x)) ξ := by
  simp only [inverseQuadratic, Matrix.toBilin_apply, Pi.basisFun_repr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem isCompact_metricUnitNull_coordinates (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (c : M) {K : Set CoordinateSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    IsCompact {p ∈ unitNull (metricComponents (coordinateMetric r c))
      (metricComponents (coordinateBilinear g c)) | p.1 ∈ K} := by
  apply isCompact_unitNull_over _ _ hK
  · exact continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      ((contDiffOn_metricComponents r c i j).continuousOn).mono hKt
  · exact (ManifoldBilinear.continuousOn_components g hg c).mono hKt
  · exact fun x hx => coordinateMetric_posDef r c (hKt hx)
  · exact fun x hx => ManifoldVolumeRegularity.coordinate_det_ne_zero g hgn c (hKt hx)

abbrev chartDomain (c : M) := (chartAt CoordinateSpace c).target

def chartUnitNull (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M)) (c : M) :
    Set (chartDomain c × Covector) :=
  unitNull (fun y : chartDomain c => metricComponents (coordinateMetric r c) y)
    (fun y : chartDomain c => metricComponents (coordinateBilinear g c) y)

theorem isCompact_chartUnitNull_preimage (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (c : M) {K : Set (chartDomain c)} (hK : IsCompact K) :
    IsCompact {p : chartUnitNull r g c | (p : chartDomain c × Covector).1 ∈ K} := by
  apply isCompact_unitNullSubtype_preimage _ _ hK
  · have hR : ContinuousOn (metricComponents (coordinateMetric r c)) (chartAt CoordinateSpace c).target :=
      continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (contDiffOn_metricComponents r c i j).continuousOn
    exact hR.comp continuous_subtype_val.continuousOn (fun y _ => y.property)
  · exact (ManifoldBilinear.continuousOn_components g hg c).comp
      continuous_subtype_val.continuousOn (fun y _ => y.property)
  · exact fun x _ => coordinateMetric_posDef r c x.property
  · exact fun x _ => ManifoldVolumeRegularity.coordinate_det_ne_zero g hgn c x.property

end Burnett.Geometry.UnitNullCompactness

namespace Burnett.Geometry.UnitNullCompactness

open Bundle Set LinearMap Module
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric ManifoldMetricTransition
open Burnett.Geometry.InverseField (matrixInverse)
open scoped Manifold ContDiff BigOperators Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

abbrev CotangentModel := CoordinateSpace →L[ℝ] ℝ

abbrev CotangentFiber (m : M) := TangentSpace Model m →L[ℝ] Bundle.Trivial M ℝ m

/-- The continuous dual of the actual tangent bundle, with its Hom vector bundle topology. -/
abbrev CotangentBundle (M : Type*) [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M] :=
  TotalSpace CotangentModel (CotangentFiber (M := M))

theorem continuous_cotangent_projection : Continuous (fun p : CotangentBundle M => p.proj) :=
  FiberBundle.continuous_proj CotangentModel (CotangentFiber (M := M))

def covectorCLM (ξ : Covector) : CotangentModel :=
  ∑ i : Index, ξ i • EuclideanSpace.proj i

theorem covectorCLM_apply_basis (ξ : Covector) (i : Index) :
    covectorCLM ξ (coordinateBasis i) = ξ i := by
  simp [covectorCLM, ContinuousLinearMap.sum_apply, coordinateBasis,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

theorem continuous_covectorCLM : Continuous covectorCLM := by
  unfold covectorCLM
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

private theorem covectorCLM_reconstruct (f : CotangentModel) :
    covectorCLM (fun i => f (coordinateBasis i)) = f := by
  ext v
  have h := congrArg f (coordinateBasis.sum_repr v)
  rw [map_sum] at h
  have hrepr (i : Index) : coordinateBasis.repr v i = v i := rfl
  simp only [map_smul, smul_eq_mul, hrepr] at h
  have hp (i : Index) : EuclideanSpace.proj (𝕜 := ℝ) i v = v i := rfl
  calc
    _ = ∑ i, v i * f (coordinateBasis i) := by
      simp only [covectorCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hp]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = _ := h

private def frameBasis (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    Basis Index ℝ (TangentSpace Model m) :=
  coordinateBasis.map
    ((trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ m hm).symm.toLinearEquiv

private theorem frameBasis_apply (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) (i : Index) :
    frameBasis c m hm i = tangentFrame c m (coordinateBasis i) := by
  rw [frameBasis, Basis.map_apply]
  rfl

private def fiberBilin (g : ManifoldBilinear.Field (M := M)) (m : M) :
    LinearMap.BilinForm ℝ (TangentSpace Model m) :=
  LinearMap.mk₂ ℝ (fun u v => g m u v)
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])

/-- Evaluate the genuine fiberwise inverse lowering map on a covector. -/
def dualEnergy (g : ManifoldBilinear.Field (M := M)) (hn : ManifoldBilinear.IsNondegenerate g)
    (p : CotangentBundle M) : ℝ :=
  p.2 (FiberMetric.sharp (fiberBilin g p.1) (hn p.1)
    (frameBasis p.1 p.1 (mem_chart_source CoordinateSpace p.1)) p.2.toLinearMap)

theorem dualEnergy_in_basis (g : ManifoldBilinear.Field (M := M)) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (p : CotangentBundle M)
    (b : Basis Index ℝ (TangentSpace Model p.1)) :
    dualEnergy g hn p = symbolNorm (matrixInverse (FiberMetric.covariant (fiberBilin g p.1) b))
      (FiberMetric.covector b p.2.toLinearMap) := by
  rw [InverseField.matrixInverse_covariant (fiberBilin g p.1) (hn p.1) (⟨hs p.1⟩ : (fiberBilin g p.1).IsSymm),
    FiberMetric.symbolNorm_eq_eval_sharp]
  unfold dualEnergy FiberMetric.sharp
  rfl

def cotangentTrivialization (c : M) :
    Trivialization CotangentModel (π CotangentModel (CotangentFiber (M := M))) :=
  trivializationAt CotangentModel (CotangentFiber (M := M)) c

theorem cotangentTrivialization_baseSet (c : M) :
    (cotangentTrivialization c).baseSet = (chartAt CoordinateSpace c).source := by
  rw [cotangentTrivialization, hom_trivializationAt_baseSet]
  exact inter_univ _

theorem cotangentTrivialization_apply (c : M) (p : CotangentBundle M)
    (v : CoordinateSpace) :
    (cotangentTrivialization c p).2 v = p.2 (tangentFrame c p.1 v) := by
  rw [cotangentTrivialization, hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, tangentFrame, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply]
  simp [Bundle.Trivial.trivialization, Bundle.Trivial.homeomorphProd]

def cotangentCoords (c : M) (p : CotangentBundle M) : Covector :=
  fun i => (cotangentTrivialization c p).2 (coordinateBasis i)

theorem dualEnergy_chart (g : ManifoldBilinear.Field (M := M)) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c : M) (p : CotangentBundle M)
    (hp : p.1 ∈ (chartAt CoordinateSpace c).source) :
    dualEnergy g hn p =
      symbolNorm (matrixInverse (metricComponents (coordinateBilinear g c) (chartAt CoordinateSpace c p.1)))
        (cotangentCoords c p) := by
  rw [dualEnergy_in_basis g hn hs p (frameBasis c p.1 hp)]
  have hG : FiberMetric.covariant (fiberBilin g p.1) (frameBasis c p.1 hp) =
      metricComponents (coordinateBilinear g c) (chartAt CoordinateSpace c p.1) := by
    funext i j
    rw [metricComponents, FiberMetric.covariant, coordinateBilinear, (chartAt CoordinateSpace c).left_inv hp]
    simp [FiberMetric.covariant, frameBasis_apply, frameBilinear, fiberBilin]
  have hξ : FiberMetric.covector (frameBasis c p.1 hp) p.2.toLinearMap = cotangentCoords c p := by
    funext i
    simp [FiberMetric.covector, frameBasis_apply, cotangentCoords, cotangentTrivialization_apply c p]
  rw [hG, hξ]

end Burnett.Geometry.UnitNullCompactness

namespace Burnett.Geometry.UnitNullCompactness

open Bundle Set LinearMap
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff BigOperators Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def cotangentAssemble (c : M) (q : M × Covector) : CotangentBundle M :=
  ⟨q.1, (cotangentTrivialization c).symm q.1 (covectorCLM q.2)⟩

theorem continuousOn_cotangentAssemble (c : M) :
    ContinuousOn (cotangentAssemble c) (Prod.fst ⁻¹' (chartAt CoordinateSpace c).source) := by
  have h := (cotangentTrivialization c).continuousOn_symm
  rw [cotangentTrivialization_baseSet] at h
  have hmap : Continuous (fun q : M × Covector => (q.1, covectorCLM q.2)) :=
    continuous_fst.prodMk (continuous_covectorCLM.comp continuous_snd)
  exact h.comp hmap.continuousOn (fun p hp => ⟨hp, trivial⟩)

theorem cotangentCoords_assemble (c : M) (q : M × Covector)
    (hq : q.1 ∈ (chartAt CoordinateSpace c).source) :
    cotangentCoords c (cotangentAssemble c q) = q.2 := by
  have hmem : q.1 ∈ (cotangentTrivialization c).baseSet := by rwa [cotangentTrivialization_baseSet]
  funext i
  unfold cotangentCoords cotangentAssemble
  rw [(cotangentTrivialization c).apply_mk_symm hmem]
  exact covectorCLM_apply_basis q.2 i

theorem cotangentAssemble_coords (c : M) (p : CotangentBundle M)
    (hp : p.1 ∈ (chartAt CoordinateSpace c).source) :
    cotangentAssemble c (p.1, cotangentCoords c p) = p := by
  have hmem : p.1 ∈ (cotangentTrivialization c).baseSet := by rwa [cotangentTrivialization_baseSet]
  unfold cotangentAssemble cotangentCoords
  rw [covectorCLM_reconstruct, (cotangentTrivialization c).symm_proj_apply p hmem]

/-- The actual nonzero momenta with auxiliary norm one and vanishing spacetime quadratic. -/
def cotangentUnitNull (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) : Set (CotangentBundle M) :=
  {p | dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 1 ∧ dualEnergy g hgn p = 0}

theorem cotangentUnitNull_covector_ne_zero
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) {p : CotangentBundle M}
    (hp : p ∈ cotangentUnitNull r g hgn) : p.2 ≠ 0 := by
  intro hz
  have h := hp.1
  unfold dualEnergy at h
  rw [hz] at h
  simp at h

theorem cotangentUnitNull_mem_chart_iff
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p.1 ∈ (chartAt CoordinateSpace c).source) :
    p ∈ cotangentUnitNull r g hgn ↔
      (p.1, cotangentCoords c p) ∈ unitNull
        (fun m : M => metricComponents (coordinateMetric r c) (chartAt CoordinateSpace c m))
        (fun m : M => metricComponents (coordinateBilinear g c) (chartAt CoordinateSpace c m)) := by
  simp only [cotangentUnitNull, unitNull, Set.mem_setOf_eq]
  rw [dualEnergy_chart g hgn hs c p hp, dualEnergy_chart r.inner (GlobalLeviCivita.inner_nondegenerate r)
    r.symm c p hp]
  rfl

theorem isCompact_cotangentUnitNull_over_chart
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c : M) {K : Set M} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).source) :
    IsCompact {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K} := by
  let e := chartAt CoordinateSpace c
  let R := fun m : M => metricComponents (coordinateMetric r c) (e m)
  let G := fun m : M => metricComponents (coordinateBilinear g c) (e m)
  have hchart : ContinuousOn e K := e.continuousOn.mono hKt
  have htt : MapsTo e K e.target := fun m hm => e.map_source (hKt hm)
  have hR : ContinuousOn (metricComponents (coordinateMetric r c)) e.target :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (contDiffOn_metricComponents r c i j).continuousOn
  have hG : ContinuousOn (metricComponents (coordinateBilinear g c)) e.target :=
    ManifoldBilinear.continuousOn_components g hg c
  have hcoord : IsCompact {q ∈ unitNull R G | q.1 ∈ K} :=
    isCompact_unitNull_over R G hK (hR.comp hchart htt) (hG.comp hchart htt)
      (fun m hm => coordinateMetric_posDef r c (htt hm))
      (fun m hm => ManifoldVolumeRegularity.coordinate_det_ne_zero g hgn c (htt hm))
  have hre : {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K} =
      cotangentAssemble c '' {q ∈ unitNull R G | q.1 ∈ K} := by
    ext p
    constructor
    · rintro ⟨hn, hk⟩
      have hp := hKt hk
      exact ⟨(p.1, cotangentCoords c p), ⟨(cotangentUnitNull_mem_chart_iff r g hgn hs c p hp).mp hn, hk⟩,
        cotangentAssemble_coords c p hp⟩
    · rintro ⟨q, ⟨hn, hk⟩, rfl⟩
      have hq : q.1 ∈ e.source := hKt hk
      have hcoords := cotangentCoords_assemble c q hq
      have hb := (cotangentUnitNull_mem_chart_iff r g hgn hs c (cotangentAssemble c q) hq).mpr
      refine ⟨hb ?_, hk⟩
      change (q.1, cotangentCoords c (cotangentAssemble c q)) ∈ unitNull R G
      rw [hcoords]
      exact hn
  rw [hre]
  exact hcoord.image_of_continuousOn ((continuousOn_cotangentAssemble c).mono (fun q hq => hKt hq.2))

theorem isCompact_cotangentUnitNull_over [T2Space M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) {K : Set M} (hK : IsCompact K) :
    IsCompact {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K} := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  have hN (c : M) : ∃ V : Set M, IsCompact V ∧ c ∈ interior V ∧ V ⊆ (chartAt CoordinateSpace c).source :=
    exists_compact_subset (chartAt CoordinateSpace c).open_source (mem_chart_source CoordinateSpace c)
  choose V hVc hVi hVs using hN
  obtain ⟨F, _, hF⟩ := hK.elim_nhds_subcover V (fun m _ => mem_interior_iff_mem_nhds.mp (hVi m))
  have hEq : {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K} =
      ⋃ c ∈ F, {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K ∩ V c} := by
    ext p
    constructor
    · rintro ⟨hn, hk⟩
      obtain ⟨c, hc, hp⟩ := mem_iUnion₂.mp (hF hk)
      exact mem_iUnion₂.mpr ⟨c, hc, hn, hk, hp⟩
    · intro hp
      obtain ⟨c, _, hn, hk, _⟩ := mem_iUnion₂.mp hp
      exact ⟨hn, hk⟩
  rw [hEq]
  exact F.isCompact_biUnion fun c _ => isCompact_cotangentUnitNull_over_chart r g hg hgn hs c
    (hK.inter_right (hVc c).isClosed) (fun _ hm => hVs c hm.2)

theorem isCompact_cotangentUnitNullSubtype_preimage [T2Space M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) {K : Set M} (hK : IsCompact K) :
    IsCompact {p : cotangentUnitNull r g hgn | (p : CotangentBundle M).1 ∈ K} := by
  rw [Subtype.isCompact_iff]
  have hEq : Subtype.val '' {p : cotangentUnitNull r g hgn | (p : CotangentBundle M).1 ∈ K} =
      {p ∈ cotangentUnitNull r g hgn | p.1 ∈ K} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · rintro ⟨hp, hk⟩
      exact ⟨⟨p, hp⟩, hk, rfl⟩
  rw [hEq]
  exact isCompact_cotangentUnitNull_over r g hg hgn hs hK

/-- A positive continuous invariant scale and its reciprocal are bounded over compact base sets. -/
theorem exists_scale_and_inverse_bounds_over_compact [T2Space M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) {K : Set M} (hK : IsCompact K)
    (s : cotangentUnitNull r g hgn → ℝ) (hc : Continuous s) (hp : ∀ p, 0 < s p) :
    ∃ C > (0 : ℝ), ∀ p : cotangentUnitNull r g hgn, (p : CotangentBundle M).1 ∈ K →
      s p ≤ C ∧ (s p)⁻¹ ≤ C := by
  let A := {p : cotangentUnitNull r g hgn | (p : CotangentBundle M).1 ∈ K}
  have hA : IsCompact A := isCompact_cotangentUnitNullSubtype_preimage r g hg hgn hs hK
  have hInv : Continuous (fun p => (s p)⁻¹) := hc.inv₀ (fun p => (hp p).ne')
  obtain ⟨C, hC, hCs⟩ := (hA.image hc).isBounded.exists_pos_norm_le
  obtain ⟨D, _, hDs⟩ := (hA.image hInv).isBounded.exists_pos_norm_le
  refine ⟨max C D, hC.trans_le (le_max_left C D), fun p hx => ⟨?_, ?_⟩⟩
  · have h := hCs (s p) (mem_image_of_mem s hx)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h.trans (le_max_left C D))
  · have h := hDs (s p)⁻¹ (mem_image_of_mem (fun q => (s q)⁻¹) hx)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h.trans (le_max_right C D))

end Burnett.Geometry.UnitNullCompactness

namespace Burnett.Geometry.UnitNullCompactness

open Bundle Set LinearMap
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Positive radial rescaling, defined fiberwise for all real scales. -/
def cotangentScale (t : ℝ) (p : CotangentBundle M) : CotangentBundle M :=
  ⟨p.1, t • p.2⟩

theorem cotangentScale_projection (t : ℝ) (p : CotangentBundle M) :
    (cotangentScale t p).1 = p.1 := rfl

theorem cotangentScale_coords (c : M) (t : ℝ) (p : CotangentBundle M) :
    cotangentCoords c (cotangentScale t p) = t • cotangentCoords c p := by
  funext i
  simp only [cotangentCoords, cotangentTrivialization_apply, cotangentScale, ContinuousLinearMap.smul_apply,
    Pi.smul_apply]

theorem continuousOn_cotangentCoords (c : M) :
    ContinuousOn (cotangentCoords c)
      ((fun p : CotangentBundle M => p.1) ⁻¹' (chartAt CoordinateSpace c).source) := by
  have h := (cotangentTrivialization c).continuousOn.snd
  rw [(cotangentTrivialization c).source_eq, cotangentTrivialization_baseSet] at h
  apply continuousOn_pi.mpr
  intro i
  exact (ContinuousLinearMap.apply ℝ ℝ (coordinateBasis i)).continuous.comp_continuousOn h

theorem continuous_cotangentScale :
    Continuous (fun q : ℝ × CotangentBundle M => cotangentScale q.1 q.2) := by
  let base := fun q : ℝ × CotangentBundle M => q.2.1
  let U := fun c : M => base ⁻¹' (chartAt CoordinateSpace c).source
  have hbase : Continuous base := continuous_cotangent_projection.comp continuous_snd
  apply continuous_of_cover_nhds (s := U)
  · intro q
    exact ⟨base q, ((chartAt CoordinateSpace (base q)).open_source.preimage hbase).mem_nhds
      (mem_chart_source CoordinateSpace (base q))⟩
  · intro c
    have hc : ContinuousOn (fun q : ℝ × CotangentBundle M => cotangentCoords c q.2) (U c) :=
      (continuousOn_cotangentCoords c).comp continuous_snd.continuousOn (fun q hq => hq)
    have ht : ContinuousOn (fun q : ℝ × CotangentBundle M => (q.1 • cotangentCoords c q.2)) (U c) :=
      continuous_fst.continuousOn.smul hc
    have hv : ContinuousOn (fun q : ℝ × CotangentBundle M => (q.2.1, q.1 • cotangentCoords c q.2)) (U c) :=
      hbase.continuousOn.prodMk ht
    refine ((continuousOn_cotangentAssemble c).comp hv (fun _ hq => hq)).congr ?_
    intro q hq
    have h : (cotangentScale q.1 q.2).1 ∈ (chartAt CoordinateSpace c).source := hq
    exact (cotangentAssemble_coords c (cotangentScale q.1 q.2) h).symm.trans (by
      rw [cotangentScale_coords, cotangentScale_projection]
      rfl)

theorem dualEnergy_cotangentScale (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (t : ℝ) (p : CotangentBundle M) :
    dualEnergy g hgn (cotangentScale t p) = t^2 * dualEnergy g hgn p := by
  have hsmul : (t • p.2).toLinearMap = t • p.2.toLinearMap := rfl
  simp only [dualEnergy, cotangentScale, hsmul, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

/-- The geometric section of the punctured null bundle for a positive choice of scale. -/
def cotangentSection (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) : CotangentBundle M :=
  cotangentScale (s p) p.1

theorem continuous_cotangentSection (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ) (hs : Continuous s) :
    Continuous (cotangentSection r g hgn s) :=
  continuous_cotangentScale.comp (hs.prodMk continuous_subtype_val)

theorem cotangentSection_projection (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) : (cotangentSection r g hgn s p).1 = p.1.1 :=
  rfl

theorem cotangentSection_covector_ne_zero
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) (hs : s p ≠ 0) : (cotangentSection r g hgn s p).2 ≠ 0 := by
  change s p • p.1.2 ≠ 0
  exact smul_ne_zero hs (cotangentUnitNull_covector_ne_zero r g hgn p.property)

theorem cotangentSection_null (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) : dualEnergy g hgn (cotangentSection r g hgn s p) = 0 := by
  unfold cotangentSection
  simp only [dualEnergy_cotangentScale, p.property.2, mul_zero]

theorem cotangentSection_auxiliary_square (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r)
      (cotangentSection r g hgn s p) = (s p)^2 := by
  unfold cotangentSection
  simp only [dualEnergy_cotangentScale, p.property.1, mul_one]

theorem cotangentSection_weighted_square (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : cotangentUnitNull r g hgn → ℝ)
    (p : cotangentUnitNull r g hgn) (hs : s p ≠ 0) :
    ((s p)^2)⁻¹ * dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r)
      (cotangentSection r g hgn s p) = 1 := by
  rw [cotangentSection_auxiliary_square]
  exact inv_mul_cancel₀ (pow_ne_zero _ hs)

end Burnett.Geometry.UnitNullCompactness
