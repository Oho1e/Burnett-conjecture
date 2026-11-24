import Burnett.Analysis.Microlocal.Overlap.ReceivingChartJetMeasureBridge
import Burnett.Analysis.Microlocal.ComplexMeasureBorelIntegral

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1250000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open Burnett.Microlocal (complexMeasureBorelIntegral complexMeasureBorelIntegral_map_withDensity)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity
  (auxiliaryScale auxiliaryScale_pos auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Going from the source round ray to the true r-unit section and then to
the receiving round phase gives the positive-direction image by the genuine
inverse-transpose transition, at the unchanged base point. -/
theorem atlasAngularPhaseCode_receiving_ray (r : Metric (M := M)) (q : CompactChartInput M)
    (c : AtlasChart M) (z : Chart q.ball)
    (hc : projection (chartAuxiliaryCosphere r q z) ∈ c.chart.source) :
    let p := chartAuxiliaryCosphere r q z
    let x := projection p
    let T := fixedCotangentTransitionMatrix (.atPoint q.center) c x
    atlasAngularPhaseCode c p =
      (c.chart x, atlasAngularDirection (WithLp.toLp 2 (T *ᵥ roundCovector z))) := by
  intro p x T
  let s := auxiliaryScale (chartAuxiliaryInverse r q z.1) (roundCovector z)
  let v := WithLp.toLp 2 (T *ᵥ roundCovector z)
  have hs : 0 < s := auxiliaryScale_pos _ _ (chartAuxiliaryNorm_pos r q z)
  have hsrc : projection p ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  have hη : atlasChartUnitCovector c p = s • (T *ᵥ roundCovector z) := by
    rw [atlasChartUnitCovector_change (.atPoint q.center) c p hsrc hc,
      show p = chartAuxiliaryCosphere r q z from rfl, atlasChartUnitCovector_preferred_ray]
    change T *ᵥ (s • roundCovector z) = _
    exact Matrix.mulVec_smul T s (roundCovector z)
  have hv : v ≠ 0 := by
    intro hZero
    have hz : T *ᵥ roundCovector z = 0 := congrArg (fun w : CoordinateSpace => w.ofLp) hZero
    exact atlasChartUnitCovector_ne_zero c p hc (by rw [hη, hz, smul_zero])
  have hVec : WithLp.toLp 2 (atlasChartUnitCovector c p) = s • v :=
    congrArg (WithLp.toLp 2) hη
  apply Prod.ext
  · change (fixedChartPhase c p.val).1 = c.chart x
    rw [fixedChartPhase_of_mem c p.val hc]
    rfl
  · change atlasAngularDirection (WithLp.toLp 2 (atlasChartUnitCovector c p)) = atlasAngularDirection v
    rw [hVec, atlasAngularDirection_pos_smul hv hs]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Read the finite receiving-phase complex measure from the original witness.
Its value on each Borel set is the transported original ordered jet integral. -/
theorem original_receivingAtlasJetEntry_angularMeasure_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ c.chart.source)
    (i j : JetSlot) :
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let μ := (traceMeasure ν).restrict (amplitudeChartWindow r q K)
    let J (p : Cosphere r) := atlasOrderedJetEntry c A.density p i j
    let raw (z : Chart q.ball) := chartInverseCutoffComplexSquare q z * receivedOriginalJetDensity r q c ν hf z i j
    let φ := chartAuxiliaryCosphere r q
    let Θ := atlasAngularPhaseCode (r := r) c
    Integrable J τ ∧ Integrable raw μ ∧
      (τ.withDensityᵥ J).map Θ = (μ.withDensityᵥ raw).map (Θ ∘ φ) ∧
      (∀ V : Set AtlasAngularPhase, MeasurableSet V →
        ((τ.withDensityᵥ J).map Θ) V = ∫ z in (Θ ∘ φ) ⁻¹' V, raw z ∂μ) ∧
      ∀ (f : AtlasAngularPhase → ℂ), Measurable f → ∀ b : ℝ, 0 ≤ b → (∀ z, ‖f z‖ ≤ b) →
        complexMeasureBorelIntegral ((τ.withDensityᵥ J).map Θ) f = (∫ p, f (Θ p) * J p ∂τ) ∧
        (∫ p, f (Θ p) * J p ∂τ) = ∫ z, f (Θ (φ z)) * raw z ∂μ := by
  intro τ μ J raw φ Θ
  obtain ⟨hI, hRaw, hEq⟩ := original_receivingAtlasJetEntry_measure_on_compact r B g hB hg
    hsB hsG hnB hnG hconv hb hv σ hσ A hA q ν hf hRep c hK hSub i j
  have hφ : Measurable φ := (continuous_chartAuxiliaryCosphere r q).measurable
  have hΘ : Measurable Θ := atlasAngularPhaseCode_measurable r c
  have hEq' : τ.withDensityᵥ J = (μ.withDensityᵥ raw).map φ := hEq
  have hMap : (τ.withDensityᵥ J).map Θ = (μ.withDensityᵥ raw).map (Θ ∘ φ) := by
    ext V hV
    rw [hEq', VectorMeasure.map_apply _ hΘ hV, VectorMeasure.map_apply _ hφ (hΘ hV),
      VectorMeasure.map_apply _ (hΘ.comp hφ) hV]
    rfl
  refine ⟨hI, hRaw, hMap, ?_, ?_⟩
  · intro V hV
    rw [hMap, VectorMeasure.map_apply _ (hΘ.comp hφ) hV,
      withDensityᵥ_apply (show Integrable raw μ from hRaw) ((hΘ.comp hφ) hV)]
  · intro f hf b hb hBound
    have hLeft := complexMeasureBorelIntegral_map_withDensity τ Θ hΘ J hI f hf b hb hBound
    refine ⟨hLeft, hLeft.symm.trans ?_⟩
    rw [hMap]
    exact complexMeasureBorelIntegral_map_withDensity μ (Θ ∘ φ) (hΘ.comp hφ) raw hRaw f hf b hb hBound

/-- The same receiving jet entry remains integrable when a compact base set
requires finitely many original chart witnesses from the fixed cover. -/
theorem original_globalAmplitude_integrable_receivingAtlasJet_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ n, (q n).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ n, (JetSlot → ℂ) → Measure (Chart (q n).ball)) (hf : ∀ n v, IsFiniteMeasure (ν n v))
    (hRep : ∀ n, let a := q n
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν n) (hf n))
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source) (i j : JetSlot) :
    Integrable (fun p => atlasOrderedJetEntry c A.density p i j)
      (A.control.restrict (amplitudeCosphereWindow r K)) := by
  let V (n : ℕ) := (q n).cutoffLocusAbove (1 / 2)
  let L (n : ℕ) := (q n).compactCutoffLocus (1 / 2)
  let U (n : ℕ) := amplitudeCosphereWindow r (K ∩ L n)
  let J (p : Cosphere r) := atlasOrderedJetEntry c A.density p i j
  have hV (n : ℕ) : IsOpen (V n) := (q n).isOpen_cutoffLocusAbove _
  have hVL (n : ℕ) : V n ⊆ L n := (q n).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hV (fun x _ => cover.symm ▸ mem_univ x)
  have hCover : amplitudeCosphereWindow r K ⊆ ⋃ n ∈ I, U n := by
    intro p hp
    obtain ⟨n, hn, hvn⟩ := mem_iUnion₂.mp (hI hp)
    exact mem_iUnion₂.mpr ⟨n, hn, hp, hVL n hvn⟩
  have hLocal (n : ℕ) : IntegrableOn J (U n) A.control := by
    have hL : IsCompact (L n) := (q n).isCompact_compactCutoffLocus _
    have hS : IsCompact (K ∩ L n) := hK.inter_right hL.isClosed
    have hSub' : K ∩ L n ⊆ (q n).nonzeroLocus ∩ c.chart.source := fun _ hp =>
      ⟨(q n).compactCutoffLocus_subset_nonzeroLocus (by norm_num) hp.2, hSub hp.1⟩
    exact (original_receivingAtlasJetEntry_measure_on_compact r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ A hA (q n) (ν n) (hf n) (hRep n) c hS hSub' i j).1
  have hFin : IntegrableOn J (⋃ n ∈ I, U n) A.control := integrableOn_finset_iUnion.mpr (fun n _ => hLocal n)
  exact hFin.mono_set hCover

end Burnett.Microlocal.Overlap
