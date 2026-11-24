import Burnett.Analysis.Microlocal.Overlap.OriginalAngularDefectConsumer

/-! The local angular limits integrate the actual compact-base complex measures. -/

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set Filter Function MeasureTheory Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (cotangentCoords)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ComplexConjugate ContDiff Manifold Topology

open private continuous_auxiliaryUnitCovector from Burnett.Analysis.Microlocal.ChartAmplitudeMeasure

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private def angularJetChartWeight (r : Metric (M := M)) (q : CompactChartInput M)
    (a : E → E → ℂ) (i j : Index) (z : Chart q.ball) : ℂ :=
  let ξ := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
  a z.1 z.2 * (ξ i : ℂ) * (ξ j : ℂ)

/-- Evaluate the scalar principal symbol on the actual oriented ray in the chart and
multiply by both covariant components of its auxiliary unit covector. The test
is zero extended from the image of the chart phase embedding. -/
def cosphereAngularJetWeight (r : Metric (M := M)) (q : CompactChartInput M)
    (a : E → E → ℂ) (i j : Index) : Cosphere r → ℂ :=
  Function.extend (chartUnitCospherePoint r q) (angularJetChartWeight r q a i j) (fun _ => 0)

variable [T2Space M]

private theorem cosphereAngularJetWeight_chart (r : Metric (M := M)) (q : CompactChartInput M)
    (a : E → E → ℂ) (i j : Index) (z : Chart q.ball) :
    cosphereAngularJetWeight r q a i j (chartUnitCospherePoint r q z) =
      angularJetChartWeight r q a i j z :=
  (measurableEmbedding_chartAuxiliaryCosphere r q).injective.extend_apply _ _ _

theorem cosphereAngularJetWeight_eq_actual (r : Metric (M := M)) (q : CompactChartInput M)
    (a : E → E → ℂ) (hDegree : ∀ x, DegreeZero (a x)) (i j : Index) (z : Chart q.ball) :
    let p := chartUnitCospherePoint r q z
    let ξ := cotangentCoords q.center p.val
    cosphereAngularJetWeight r q a i j p =
      a (chartAt E q.center (projection p)) (WithLp.toLp 2 ξ) * (ξ i : ℂ) * (ξ j : ℂ) := by
  dsimp only
  rw [cosphereAngularJetWeight_chart]
  change angularJetChartWeight r q a i j z =
    a (chartAt E q.center ((chartAt E q.center).symm z.1))
        (WithLp.toLp 2 (cotangentCoords q.center (chartAuxiliaryRay r q z))) *
      (cotangentCoords q.center (chartAuxiliaryRay r q z) i : ℂ) *
      (cotangentCoords q.center (chartAuxiliaryRay r q z) j : ℂ)
  rw [(chartAt E q.center).right_inv (q.ball_in_chart z.1.property), chartAuxiliaryRay_coords]
  have hξ : WithLp.toLp 2 (auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)) =
      auxiliaryScale (chartAuxiliaryInverse r q z.1) (roundCovector z) • (z.2 : E) := by
    apply PiLp.ext
    intro k
    rfl
  have hScale := auxiliaryScale_pos _ _ (chartAuxiliaryNorm_pos r q z)
  rw [hξ, hDegree z.1 _ hScale]
  rfl

theorem cosphereAngularJetWeight_measurable_bounded (r : Metric (M := M)) (q : CompactChartInput M)
    (a : E → E → ℂ) (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E))) (i j : Index) :
    Measurable (cosphereAngularJetWeight r q a i j) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ‖cosphereAngularJetWeight r q a i j p‖ ≤ D := by
  have hAng : Continuous (fun z : Chart q.ball => a z.1 z.2) := by
    have hMap : Continuous (fun z : Chart q.ball => ((z.1 : E), (z.2 : E))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    apply hJoint.continuousOn.comp_continuous hMap
    intro z
    refine ⟨mem_univ _, ?_⟩
    have hNorm : ‖(z.2 : E)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
    exact norm_ne_zero_iff.mp (by rw [hNorm]; exact one_ne_zero)
  have hR (a b : Index) : Continuous (fun z => chartAuxiliaryInverse r q z a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_chartAuxiliaryInverse r q))
  have hEta (k : Index) := Complex.continuous_ofReal.comp
    (continuous_auxiliaryUnitCovector q.ball (chartAuxiliaryInverse r q) hR (chartAuxiliaryNorm_pos r q) k)
  have hCont : Continuous (angularJetChartWeight r q a i j) := (hAng.mul (hEta i)).mul (hEta j)
  let F := chartUnitCospherePoint r q
  have hF : MeasurableEmbedding F := measurableEmbedding_chartAuxiliaryCosphere r q
  refine ⟨hF.measurable_extend hCont.measurable measurable_const, ?_⟩
  obtain ⟨D, hD⟩ := (isCompact_univ.image hCont).isBounded.exists_norm_le
  refine ⟨max D 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : p ∈ range F
  · obtain ⟨z, rfl⟩ := hp
    rw [cosphereAngularJetWeight_chart]
    exact (hD _ (mem_image_of_mem _ (mem_univ z))).trans (le_max_left _ _)
  · unfold cosphereAngularJetWeight
    rw [Function.extend_apply' _ _ _ hp, norm_zero]
    exact le_max_right _ _

variable [MeasurableSpace M] [BorelSpace M]

theorem complexMeasureBorelIntegral_normalizedCosphereAmplitudeEntryOn
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E → E → ℂ) (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E))) (i j : JetSlot) :
    complexMeasureBorelIntegral (normalizedCosphereAmplitudeEntryOn r q ν hfin j.2 i.2 K)
        (cosphereAngularJetWeight r q a i.1 j.1) =
      ∫ z in amplitudeChartWindow r q K,
        let ξ := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
        (a z.1 z.2 * (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) *
          (chartInverseCutoffComplexSquare q z * chartAuxiliaryAmplitude r q ν hfin z j.2 i.2)
          ∂traceMeasure ν := by
  have hφ := (continuous_chartUnitCospherePoint r q).measurable
  have hI := integrable_normalizedCosphereAmplitudeEntry_on_compact r q ν hfin j.2 i.2 hK hSub
  obtain ⟨hTest, D, hD, hBound⟩ := cosphereAngularJetWeight_measurable_bounded r q a hJoint i.1 j.1
  unfold normalizedCosphereAmplitudeEntryOn normalizedCosphereChartEntryOn
  rw [complexMeasureBorelIntegral_map_withDensity _ _ hφ _ hI _ hTest D hD hBound]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change cosphereAngularJetWeight r q a i.1 j.1 (chartUnitCospherePoint r q z) * _ =
      angularJetChartWeight r q a i.1 j.1 z * _
    rw [cosphereAngularJetWeight_chart]

variable [SecondCountableTopology M]

/-- On the actual original volume-weighted input and the given subsequence, the
principal action with the compensating symbol is represented by the ordered
normalized complex amplitude measure on the auxiliary cosphere. -/
theorem tendsto_originalVolume_angularAction_cosphereAmplitudeEntryOn
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E → E → ℂ) (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ chartAt E q.center '' K)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (i j : JetSlot) :
    let f := originalVolumeAngularInput B g hB hg hnB q
    Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
      firstOrderAction (inverseCutoffAngularSymbol q.cutoff a) (f (σ n) j) x)
      atTop (𝓝 (complexMeasureBorelIntegral (normalizedCosphereAmplitudeEntryOn r q ν hfin j.2 i.2 K)
        (cosphereAngularJetWeight r q a i.1 j.1))) := by
  rw [complexMeasureBorelIntegral_normalizedCosphereAmplitudeEntryOn r q ν hfin hK hSub a hJoint]
  exact tendsto_originalVolume_angularAction_normalizedAmplitudeOn r B g hB hg hsB hsG hnB hnG
    hconv hb hv q σ hσ ν hfin hRep K hK hSub a hSupport hJoint hZero hDegree i j

end Burnett.Microlocal.Overlap
