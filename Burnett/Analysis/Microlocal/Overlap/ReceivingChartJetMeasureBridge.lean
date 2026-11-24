import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceReconstruction
import Burnett.Analysis.Microlocal.Overlap.GlobalAmplitudeEntryMeasure

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (continuousOn_fixedChartPhase)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors (tensorPairTransition tensorJetTransition jetCovariance_tensor_transition)
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot gradientEmbedding gradient_factor_entry)
open Burnett.Microlocal.FixedChartGeometricDensity
  (auxiliaryUnitCovector roundCovector chartPhysicalCovariance)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.F07.IntrinsicAmplitude
  (auxiliaryTraceLinear aemeasurable_auxiliaryTraceLinear auxiliaryTraceLinear_nonneg_and_eq_zero_iff
    chartAuxiliaryInverse_posDef)
open scoped ComplexConjugate ComplexOrder ContDiff ENNReal Manifold Matrix

open private isCompact_amplitudeChartWindow from Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudeOverlap
open private measurable_chartInverseCutoffSquare chartInverseCutoffSquare_toReal_smul from
  Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeTraceLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem continuousOn_atlasChartUnitCovector_entry (r : Metric (M := M)) (c : AtlasChart M)
    (i : Index) : ContinuousOn (fun p : Cosphere r => atlasChartUnitCovector c p i)
      (projection ⁻¹' c.chart.source) :=
  (continuous_apply i).comp_continuousOn
    (((continuousOn_fixedChartPhase c).comp continuous_subtype_val.continuousOn (fun _ hp => hp)).snd)

/-- The raw ordered jet density of the given original witness, read in the
receiving chart by the actual three-slot transition. -/
def receivedOriginalJetDensity (r : Metric (M := M)) (q : CompactChartInput M) (c : AtlasChart M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (z : Chart q.ball) (i j : JetSlot) : ℂ :=
  let x := projection (chartAuxiliaryCosphere r q z)
  let C := tensorJetTransition (fixedCotangentTransitionMatrix (.atPoint q.center) c x)
  (C * (density ν hf z)ᵀ * Cᴴ) j i

theorem receivedOriginalJetDensity_eq_ordered_sum (r : Metric (M := M)) (q : CompactChartInput M)
    (c : AtlasChart M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hf : ∀ v, IsFiniteMeasure (ν v)) (z : Chart q.ball) (i j : JetSlot) :
    let C := tensorJetTransition (fixedCotangentTransitionMatrix (.atPoint q.center) c
      (projection (chartAuxiliaryCosphere r q z)))
    receivedOriginalJetDensity r q c ν hf z i j =
      ∑ k : JetSlot, ∑ l : JetSlot, conj (C i k) * C j l * density ν hf z k l := by
  intro C
  simpa only [one_mul, receivedOriginalJetDensity, C] using
    (orderedJet_congruence_entry C (density ν hf z) 1 j i).symm

private theorem receivedOriginalJetDensity_factor
    (r : Metric (M := M)) (q : CompactChartInput M) (c : AtlasChart M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (z : Chart q.ball) (hc : projection (chartAuxiliaryCosphere r q z) ∈ c.chart.source)
    (hFactor : let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
      ∀ k l : JetSlot, chartPhysicalCovariance q.ball ν hf z k l =
        (η k.1 : ℂ) * (η l.1 : ℂ) * chartAuxiliaryAmplitude r q ν hf z k.2 l.2)
    (i j : JetSlot) :
    let p := chartAuxiliaryCosphere r q z
    let T := atlasAmplitudeTransition (.atPoint q.center) c (projection p)
    receivedOriginalJetDensity r q c ν hf z i j =
      (atlasChartUnitCovector c p i.1 : ℂ) * (atlasChartUnitCovector c p j.1 : ℂ) *
        (T * chartAuxiliaryAmplitude r q ν hf z * Tᴴ) j.2 i.2 := by
  intro p T
  let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
  let R := fixedCotangentTransitionMatrix (.atPoint q.center) c (projection p)
  let S := chartAuxiliaryAmplitude r q ν hf z
  have hsrc : projection p ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  have hη : atlasChartUnitCovector c p = R *ᵥ η := by
    rw [atlasChartUnitCovector_change (.atPoint q.center) c p hsrc hc]
    exact congrArg (fun v => R *ᵥ v) (atlasChartUnitCovector_preferred_ray r q z)
  have hN : (density ν hf z)ᵀ = gradientEmbedding η * S * (gradientEmbedding η)ᴴ := by
    ext k l
    exact (hFactor k l).trans (gradient_factor_entry η S k l).symm
  change (tensorJetTransition R * (density ν hf z)ᵀ * (tensorJetTransition R)ᴴ) j i = _
  rw [hN, jetCovariance_tensor_transition, gradient_factor_entry, ← hη]
  ring

private theorem withDensityᵥ_map_measurableEmbedding {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (φ : X → Y) (hφ : MeasurableEmbedding φ) (g : Y → ℂ)
    (hg : Integrable g (μ.map φ)) :
    (μ.map φ).withDensityᵥ g = (μ.withDensityᵥ (g ∘ φ)).map φ := by
  have hPull := hφ.integrable_map_iff.mp hg
  ext S hS
  rw [withDensityᵥ_apply hg hS, VectorMeasure.map_apply _ hφ.measurable hS,
    withDensityᵥ_apply hPull (hφ.measurable hS), hφ.setIntegral_map]
  rfl

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The receiver's true ordered jet entry is read from the same represented
source witness on a compact base window. The equality holds as a complex
measure before the receiving angle map is applied. -/
theorem original_receivingAtlasJetEntry_measure_on_compact
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
    Integrable J τ ∧ Integrable raw μ ∧
      τ.withDensityᵥ J = (μ.withDensityᵥ raw).map (chartAuxiliaryCosphere r q) := by
  intro τ μ J raw
  let d : AtlasChart M := .atPoint q.center
  let W := amplitudeCosphereWindow r K
  let U := amplitudeChartWindow r q K
  let φ := chartAuxiliaryCosphere r q
  let κ := μ.withDensity (chartInverseCutoffSquare q)
  let rawControl := κ.map φ
  let S := liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
  let R := liftChartAuxiliaryInverse r q
  let t := chartAmplitudeTraceWeight r q ν hf
  let E (p : Cosphere r) := ENNReal.ofReal (t p)
  let T (p : Cosphere r) := atlasAmplitudeTransition d c (projection p)
  let F (p : Cosphere r) := (atlasChartUnitCovector c p i.1 : ℂ) * (atlasChartUnitCovector c p j.1 : ℂ)
  let v (p : Cosphere r) := F p * (T p * S p * (T p)ᴴ) j.2 i.2
  have hφ : MeasurableEmbedding φ := measurableEmbedding_chartAuxiliaryCosphere r q
  have hKm := hK.isClosed.measurableSet
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hKm
  have hU : MeasurableSet U := measurableSet_amplitudeChartWindow r q hKm
  have hControlMap : (chartCosphereControlMeasure r q ν).restrict W = rawControl :=
    chartCosphereControlMeasure_restrict r q ν hKm
  have hQ : K ⊆ q.nonzeroLocus := hSub.trans inter_subset_left
  have hCd : K ⊆ d.chart.source ∩ c.chart.source := fun _ hp => ⟨(hSub hp).1.1, (hSub hp).2⟩
  obtain ⟨hControl, hField⟩ := hA q ν hf hRep K hK hQ
  have hτ : τ = rawControl.withDensity E := hControl.trans (by
    rw [chartAmplitudeTraceControl, restrict_withDensity hW, hControlMap])
  have hFieldτ : ∀ᵐ p ∂τ, A.density p = chartNormalizedIntrinsicAmplitude r q ν hf p := by
    change ∀ᵐ p ∂A.control.restrict W, _
    rw [hControl]
    exact hField
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv q σ hσ ν hf hRep
  have hCutAC : κ ≪ μ := withDensity_absolutelyContinuous _ _
  have hOn : ∀ᵐ p ∂rawControl, ∃ z ∈ U, φ z = p ∧ (chartAuxiliaryAmplitude r q ν hf z).PosSemidef := by
    apply hφ.ae_map_iff.mpr
    filter_upwards [hCutAC.ae_le (ae_restrict_mem (μ := traceMeasure ν) hU),
      hCutAC.ae_le (ae_restrict_of_ae hData)] with z hz hD
    exact ⟨z, hz, rfl, hD.1⟩
  have hAC : τ ≪ rawControl := hτ.symm ▸ withDensity_absolutelyContinuous rawControl E
  have hSource (a b) : Integrable (fun p => atlasAmplitudeMatrix d A.density p a b) τ :=
    (original_globalAmplitude_entryMeasure_on_compactChart r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ A hA q ν hf hRep hK hQ a b).1
  have hAInt := integrable_atlasAmplitudeMatrix_change_on_compact r d c A.density A.control
    hK hCd hSource j.2 i.2
  have hComp (k : Index) : ContinuousOn (fun p : Cosphere r => (atlasChartUnitCovector c p k : ℂ)) W :=
    Complex.continuous_ofReal.comp_continuousOn ((continuousOn_atlasChartUnitCovector_entry r c k).mono
      (preimage_mono (hCd.trans inter_subset_right)))
  have hF : ContinuousOn F W := (hComp i.1).mul (hComp j.1)
  have hFpull : ContinuousOn (F ∘ φ) U := hF.comp
    (continuous_chartAuxiliaryCosphere r q).continuousOn (fun _ hz => hz)
  obtain ⟨b, hBound⟩ := ((isCompact_amplitudeChartWindow r q hK).image_of_continuousOn hFpull).isBounded.exists_norm_le
  have hJ : Integrable J τ := by
    apply hAInt.bdd_mul' (hF.aemeasurable hW).aestronglyMeasurable
    filter_upwards [hAC.ae_le hOn] with p hp
    obtain ⟨z, hz, rfl, _⟩ := hp
    exact hBound _ (mem_image_of_mem (F ∘ φ) hz)
  have hD : J =ᵐ[τ] fun p => (t p)⁻¹ • v p := by
    filter_upwards [hFieldτ, hAC.ae_le hOn] with p hp hGeom
    obtain ⟨z, hz, rfl, _⟩ := hGeom
    let p := φ z
    have hBase : projection p ∈ K := hz
    have hs := (hCd hBase).1
    have hSrc : atlasAmplitudeMatrix d A.density p = (t p)⁻¹ • S p := by
      rw [show d = .atPoint q.center from rfl, atlasAmplitudeMatrix_preferred,
        intrinsicAmplitudeMatrix_of_mem q.center A.density p hs, hp,
        ← intrinsicAmplitudeMatrix_of_mem q.center _ p hs]
      exact intrinsicAmplitudeMatrix_chartNormalized_of_mem r q ν hf p hs
    change F p * atlasAmplitudeMatrix c A.density p j.2 i.2 = (t p)⁻¹ • v p
    rw [atlasAmplitudeMatrix_change d c A.density p hs (hCd hBase).2, hSrc]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Algebra.mul_smul_comm, v, T]
  have hTmeas : AEMeasurable t rawControl := aemeasurable_auxiliaryTraceLinear rawControl R S
    (fun a b => (measurable_liftChartAuxiliaryInverse_entry r q a b).aemeasurable)
    (fun a b => (measurable_liftChartAmplitude_entry r q (chartAuxiliaryAmplitude r q ν hf) a b
      (measurable_chartAuxiliaryAmplitude_entry r q ν hf a b)).aemeasurable)
  have hE : AEMeasurable E rawControl := ENNReal.measurable_ofReal.comp_aemeasurable hTmeas
  have hEfin : ∀ᵐ p ∂rawControl, E p < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hJnorm : Integrable J (rawControl.withDensity E) := hτ ▸ hJ
  have hSmulInt := (integrable_withDensity_iff_integrable_smul₀' hE hEfin).mp hJnorm
  have hDnorm : J =ᵐ[rawControl.withDensity E] fun p => (t p)⁻¹ • v p := by
    rw [← hτ]
    exact hD
  have hDimp := (ae_withDensity_iff' hE).mp hDnorm
  have hRecover : (fun p => (E p).toReal • J p) =ᵐ[rawControl] v := by
    filter_upwards [hDimp, hOn] with p hp hGeom
    obtain ⟨z, _, rfl, hPSD⟩ := hGeom
    let p := φ z
    have hRp : Matrix.PosDef (R p) := by
      change Matrix.PosDef (liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r q z))
      rw [liftChartAuxiliaryInverse_apply]
      exact chartAuxiliaryInverse_posDef r q z
    have hSp : (S p).PosSemidef := by
      change (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z)).PosSemidef
      rw [liftChartAmplitude_apply]
      exact hPSD
    obtain ⟨htNN, htZero⟩ := auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R p) hRp (S p) hSp
    change 0 ≤ t p at htNN
    change t p = 0 ↔ S p = 0 at htZero
    change (ENNReal.ofReal (t p)).toReal • J p = v p
    rw [ENNReal.toReal_ofReal htNN]
    by_cases ht : t p = 0
    · have hS := htZero.mp ht
      simp only [ht, zero_smul, v, hS, Matrix.zero_mul, Matrix.zero_apply, mul_zero]
    · have ht' : E p ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne htNN (fun hz => ht hz.symm))).ne'
      have hJv := hp ht'
      change J p = (t p)⁻¹ • v p at hJv
      rw [hJv, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hvInt : Integrable v rawControl := hSmulInt.congr hRecover
  have hOriginal : τ.withDensityᵥ J = rawControl.withDensityᵥ v := by
    rw [hτ, ← withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hE hEfin hSmulInt]
    exact WithDensityᵥEq.congr_ae hRecover
  have hvPull : Integrable (v ∘ φ) κ := hφ.integrable_map_iff.mp hvInt
  have hχ := measurable_chartInverseCutoffSquare q
  have hχfin : ∀ᵐ z ∂μ, chartInverseCutoffSquare q z < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hχInt := (integrable_withDensity_iff_integrable_smul' hχ hχfin).mp hvPull
  have hRaw : (fun z => (chartInverseCutoffSquare q z).toReal • (v ∘ φ) z) =ᵐ[μ] raw := by
    filter_upwards [ae_restrict_of_ae (s := U) hData, ae_restrict_mem (μ := traceMeasure ν) hU]
      with z hNz hz
    have hp : projection (φ z) ∈ K := hz
    have h := receivedOriginalJetDensity_factor r q c ν hf z (hCd hp).2 hNz.2.1 i j
    have he : v (φ z) = receivedOriginalJetDensity r q c ν hf z i j := by
      refine (?_ : v (φ z) = _).trans h.symm
      change F (φ z) * (T (φ z) * liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
        (chartAuxiliaryCosphere r q z) * (T (φ z))ᴴ) j.2 i.2 = _
      rw [liftChartAmplitude_apply]
    change (chartInverseCutoffSquare q z).toReal • v (φ z) = raw z
    rw [he]
    exact chartInverseCutoffSquare_toReal_smul q z _
  refine ⟨hJ, hχInt.congr hRaw, hOriginal.trans ?_⟩
  calc
    rawControl.withDensityᵥ v = (κ.withDensityᵥ (v ∘ φ)).map φ :=
      withDensityᵥ_map_measurableEmbedding κ φ hφ v hvInt
    _ = (μ.withDensityᵥ raw).map φ := by
      apply congrArg (fun m : ComplexMeasure (Chart q.ball) => m.map φ)
      exact (withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hχ.aemeasurable hχfin hχInt).symm.trans
        (WithDensityᵥEq.congr_ae hRaw)

end Burnett.Microlocal.Overlap
