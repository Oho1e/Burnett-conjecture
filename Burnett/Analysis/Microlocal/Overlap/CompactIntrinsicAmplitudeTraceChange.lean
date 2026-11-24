import Burnett.Analysis.Microlocal.Overlap.AuxiliaryAmplitudeTraceChangeCore
import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudePositiveKernel

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1050000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open MaximalChart (AtlasChart)
open UnitCosphere (Cosphere projection)
open CotangentAngularExtension (cotangentNorm_sq auxiliary_dualEnergy_pos)
open CotangentUnitNormalization (unitShell_punctured)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeFiber chartAmplitude chartComponents chartComponents_chartAmplitude chartComponents_injective)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.F07.IntrinsicAmplitude
  (aemeasurable_auxiliaryTraceLinear auxiliaryTraceLinear auxiliaryTraceLinear_apply
    chartAuxiliaryInverse_posDef orderedChartAmplitudeComponents)
open scoped ComplexOrder ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem chartAmplitude_real_smul (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source)
    (u : ℝ) (A : Matrix Pair Pair ℂ) :
    chartAmplitude c x hx (u • A) = u • chartAmplitude c x hx A := by
  apply chartComponents_injective c x hx
  have hc (T : AmplitudeFiber x) : chartComponents c x hx (u • T) = u • chartComponents c x hx T := by
    ext i j
    rfl
  rw [hc, chartComponents_chartAmplitude, chartComponents_chartAmplitude]

private theorem cast_chartAmplitude (c : AtlasChart M) {x y : M} (h : x = y)
    (hx : x ∈ c.chart.source) (hy : y ∈ c.chart.source) (A : Matrix Pair Pair ℂ) :
    cast (congrArg (fun z : M => AmplitudeFiber z) h) (chartAmplitude c x hx A) =
      chartAmplitude c y hy A := by
  subst y
  rfl

private theorem real_smul_complex_matrix (s : ℝ) (A : Matrix Pair Pair ℂ) :
    (s : ℂ) • A = s • A := by
  ext i j
  exact (Complex.real_smul (x := s) (z := A i j)).symm

private theorem matrix_normalized_change_trace (A : Matrix Pair Pair ℂ) {a b s : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) :
    (s * b)⁻¹ • ((s : ℂ) • A) = (a⁻¹ * b)⁻¹ • (a⁻¹ • A) := by
  rw [real_smul_complex_matrix, smul_smul, smul_smul]
  have h : (s * b)⁻¹ * s = (a⁻¹ * b)⁻¹ * a⁻¹ := by field_simp [ha, hb, hs]
  rw [h]

variable [T2Space M]

private theorem measurable_intrinsic_chart_trace_weight
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v)) :
    Measurable (chartAmplitudeTraceWeight r q ν hf) := by
  change Measurable (fun p => auxiliaryTraceLinear (liftChartAuxiliaryInverse r q p)
    (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p))
  simp only [auxiliaryTraceLinear_apply]
  refine Finset.measurable_fun_sum _ (fun i _ => Finset.measurable_fun_sum _ (fun j _ => ?_))
  exact ((measurable_liftChartAuxiliaryInverse_entry r q i.1 j.1).mul
    (measurable_liftChartAuxiliaryInverse_entry r q i.2 j.2)).mul
    (Complex.continuous_re.measurable.comp (measurable_liftChartAmplitude_entry r q
      (chartAuxiliaryAmplitude r q ν hf) i j (measurable_chartAuxiliaryAmplitude_entry r q ν hf i j)))

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- On a compact window of the same represented chart, the new control gains
the squared radial factor and the new trace of the old normalized tensor.
The new normalized tensor divides the old tensor by exactly this trace. -/
theorem original_intrinsicAmplitude_trace_changeAuxiliary_on_compactChart
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (A' : IntrinsicAmplitudeCovariance r')
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hSig.isNondegenerate σ A)
    (hA' : HasOriginalAmplitudeChartLaws r' B g hB hg hSig.isNondegenerate σ A')
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let τ' := A'.control.restrict (amplitudeCosphereWindow r' K)
    let F := renormalizeUnitCosphere r r'
    let t := intrinsicAmplitudeTraceInMetric r r' A.density
    AEMeasurable t τ ∧ (∀ᵐ p ∂τ, 0 < t p) ∧
      τ' = (τ.withDensity (fun p => cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (t p))).map F ∧
      (∀ᵐ p ∂τ, pullbackAmplitudeDensity r r' A'.density p = (t p)⁻¹ • A.density p) := by
  intro τ τ' F t
  let W := amplitudeCosphereWindow r K
  let W' := amplitudeCosphereWindow r' K
  let raw := (chartCosphereControlMeasure r q ν).restrict W
  let raw' := (chartCosphereControlMeasure r' q ν).restrict W'
  let s (p : Cosphere r) := dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') p.val
  let S := liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
  let S' := liftChartAmplitude r' q (chartAuxiliaryAmplitude r' q ν hf)
  let R := liftChartAuxiliaryInverse r q
  let R' (p : Cosphere r) := liftChartAuxiliaryInverse r' q (F p)
  let a := chartAmplitudeTraceWeight r q ν hf
  let a' := chartAmplitudeTraceWeight r' q ν hf
  let b (p : Cosphere r) := auxiliaryTraceLinear (R' p) (S p)
  let ratio (p : Cosphere r) := (a p)⁻¹ * b p
  have hKm := hK.isClosed.measurableSet
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hKm
  have hW' : MeasurableSet W' := measurableSet_amplitudeCosphereWindow r' hKm
  have hF : MeasurableEmbedding F := measurableEmbedding_renormalizeUnitCosphere r r'
  have hPhase (z : Chart q.ball) : F (chartAuxiliaryCosphere r q z) = chartAuxiliaryCosphere r' q z :=
    (congrFun (chartAuxiliaryCosphere_changeAuxiliary r r' q) z).symm
  have hs : Measurable s := ((continuous_auxiliaryDualSquare r').comp continuous_subtype_val).measurable
  have hsPos (p : Cosphere r) : 0 < s p := auxiliary_dualEnergy_pos r' (unitShell_punctured r p.property)
  have hOld := hA q ν hf hRep K hK hSub
  have hNew := hA' q ν hf hRep K hK hSub
  have hτ : τ = raw.withDensity (fun p => ENNReal.ofReal (a p)) := hOld.1.trans (by
    rw [chartAmplitudeTraceControl, restrict_withDensity hW])
  have hτ' : τ' = raw'.withDensity (fun p => ENNReal.ofReal (a' p)) := hNew.1.trans (by
    rw [chartAmplitudeTraceControl, restrict_withDensity hW'])
  have hAC : τ ≪ raw := hτ.symm ▸ withDensity_absolutelyContinuous raw _
  have hOldD : ∀ᵐ p ∂τ, A.density p = chartNormalizedIntrinsicAmplitude r q ν hf p := by
    change ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), _
    rw [hOld.1]
    exact hOld.2
  have hNewD : ∀ᵐ p ∂τ', A'.density p = chartNormalizedIntrinsicAmplitude r' q ν hf p := by
    change ∀ᵐ p ∂A'.control.restrict (amplitudeCosphereWindow r' K), _
    rw [hNew.1]
    exact hNew.2
  have hAmpChart := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hf hRep
  have hChangeChart := ae_original_chartAuxiliaryAmplitude_changeAuxiliary r r' B g hB hg hSig hsG hnG
    hconv hb hv q σ hσ ν hf hRep
  have hGeometry : ∀ᵐ p ∂raw, ∃ z : Chart q.ball, chartAuxiliaryCosphere r q z = p ∧
      (chartAuxiliaryAmplitude r q ν hf z).PosSemidef ∧ S' (F p) = (s p : ℂ) • S p := by
    change ∀ᵐ p ∂(chartCosphereControlMeasure r q ν).restrict W, _
    rw [chartCosphereControlMeasure_restrict r q ν hKm]
    apply (measurableEmbedding_chartAuxiliaryCosphere r q).ae_map_iff.mpr
    have hCut := withDensity_absolutelyContinuous ((traceMeasure ν).restrict (amplitudeChartWindow r q K))
      (chartInverseCutoffSquare q)
    filter_upwards [hCut.ae_le (ae_restrict_of_ae hAmpChart),
      hCut.ae_le (ae_restrict_of_ae hChangeChart)] with z hD hChange
    refine ⟨z, rfl, hD.1, ?_⟩
    change liftChartAmplitude r' q (chartAuxiliaryAmplitude r' q ν hf)
      (F (chartAuxiliaryCosphere r q z)) =
      (s (chartAuxiliaryCosphere r q z) : ℂ) •
        liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z)
    rw [hPhase, liftChartAmplitude_apply, liftChartAmplitude_apply]
    have hEnergy := cotangentNorm_sq r' (unitShell_punctured r (chartAuxiliaryRay_unit r q z))
    rw [hEnergy] at hChange
    exact hChange
  have hPositive : ∀ᵐ p ∂raw, Matrix.PosDef (R p) ∧ Matrix.PosDef (R' p) ∧ (S p).PosSemidef := by
    filter_upwards [hGeometry] with p hp
    obtain ⟨z, rfl, hz, _⟩ := hp
    change Matrix.PosDef (liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r q z)) ∧
      Matrix.PosDef (liftChartAuxiliaryInverse r' q (F (chartAuxiliaryCosphere r q z))) ∧
      (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z)).PosSemidef
    rw [hPhase, liftChartAuxiliaryInverse_apply, liftChartAuxiliaryInverse_apply, liftChartAmplitude_apply]
    exact ⟨chartAuxiliaryInverse_posDef r q z, chartAuxiliaryInverse_posDef r' q z, hz⟩
  have ha : AEMeasurable a raw := (measurable_intrinsic_chart_trace_weight r q ν hf).aemeasurable
  have ha' : Measurable a' := measurable_intrinsic_chart_trace_weight r' q ν hf
  have hbMeas : AEMeasurable b raw := aemeasurable_auxiliaryTraceLinear raw R' S
    (fun i j => ((measurable_liftChartAuxiliaryInverse_entry r' q i j).comp hF.measurable).aemeasurable)
    (fun i j => (measurable_liftChartAmplitude_entry r q (chartAuxiliaryAmplitude r q ν hf) i j
      (measurable_chartAuxiliaryAmplitude_entry r q ν hf i j)).aemeasurable)
  have hTraceScaled : (fun p => a' (F p)) =ᵐ[raw] fun p => s p * b p := by
    filter_upwards [hGeometry] with p hp
    obtain ⟨_, _, _, hAmp⟩ := hp
    change auxiliaryTraceLinear (R' p) (S' (F p)) = s p * b p
    rw [hAmp, real_smul_complex_matrix, map_smul, smul_eq_mul]
  obtain ⟨hRatio, hTracesPos, hWeighted⟩ := auxiliaryTrace_normalization_change_control raw R R' S s
    hPositive ha hbMeas hs.aemeasurable (Filter.Eventually.of_forall fun p => (hsPos p).le)
  have hTracesPosτ : ∀ᵐ p ∂τ, 0 < a p ∧ 0 < b p := hτ.symm ▸ hTracesPos
  have hRatioPos : ∀ᵐ p ∂τ, 0 < ratio p :=
    hTracesPosτ.mono (fun _ hp => mul_pos (inv_pos.mpr hp.1) hp.2)
  have hT : t =ᵐ[τ] ratio := by
    filter_upwards [hOldD, hAC.ae_le hGeometry] with p hp hGeom
    obtain ⟨z, rfl, _, _⟩ := hGeom
    have hComponents := orderedChartAmplitudeComponents_eq_original_of_density_eq r q ν hf A.density z hp
    calc
      _ = auxiliaryTraceLinear (chartAuxiliaryInverse r' q z.1)
          (orderedChartAmplitudeComponents r q A.density z) :=
        intrinsicAmplitudeTraceInMetric_eq_chart r r' q A.density z
      _ = ratio (chartAuxiliaryCosphere r q z) := by
        change _ = (a (chartAuxiliaryCosphere r q z))⁻¹ *
          auxiliaryTraceLinear (liftChartAuxiliaryInverse r' q (F (chartAuxiliaryCosphere r q z)))
            (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z))
        rw [hComponents, map_smul, smul_eq_mul, hPhase, liftChartAuxiliaryInverse_apply, liftChartAmplitude_apply]
  let w (p : Cosphere r) := ENNReal.ofReal (s p) * ENNReal.ofReal (ratio p)
  have hRawMap : raw' = raw.map F := chartCosphereControlMeasure_restrict_changeAuxiliary r r' q ν hKm
  have hMeasure : τ' = (τ.withDensity w).map F := by
    calc
      τ' = (raw.map F).withDensity (fun p => ENNReal.ofReal (a' p)) := by rw [hτ', hRawMap]
      _ = (raw.withDensity (fun p => ENNReal.ofReal (a' (F p)))).map F :=
        map_withDensity_comp F hF.measurable raw _ (ENNReal.measurable_ofReal.comp ha')
      _ = (raw.withDensity (fun p => ENNReal.ofReal (s p * b p))).map F :=
        congrArg (Measure.map F) (withDensity_congr_ae (hTraceScaled.fun_comp ENNReal.ofReal))
      _ = (τ.withDensity w).map F := by
        apply congrArg (Measure.map F)
        exact hWeighted.trans (congrArg (fun m : Measure (Cosphere r) => m.withDensity w) hτ.symm)
  have hLaw : τ' = (τ.withDensity (fun p => cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (t p))).map F :=
    hMeasure.trans (congrArg (Measure.map F) (withDensity_congr_ae (hT.mono fun p hp => by
      change ENNReal.ofReal (s p) * ENNReal.ofReal (ratio p) =
        ENNReal.ofReal (s p) * ENNReal.ofReal (t p)
      rw [hp])))
  refine ⟨(hRatio.mono_ac hAC).congr hT.symm,
    (hRatioPos.and hT).mono (fun _ hp => hp.2.symm ▸ hp.1), hLaw, ?_⟩
  have hTiltAC : τ ≪ τ.withDensity w := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp hs).aemeasurable.mul
        (ENNReal.measurable_ofReal.comp_aemeasurable (hRatio.mono_ac hAC))
    · exact hRatioPos.mono fun p hp => mul_ne_zero (ENNReal.ofReal_pos.mpr (hsPos p)).ne'
        (ENNReal.ofReal_pos.mpr hp).ne'
  have hNewOnMap : ∀ᵐ p ∂(τ.withDensity w).map F,
      A'.density p = chartNormalizedIntrinsicAmplitude r' q ν hf p := hMeasure ▸ hNewD
  have hNewAlong : ∀ᵐ p ∂τ, A'.density (F p) = chartNormalizedIntrinsicAmplitude r' q ν hf (F p) := by
    have h := hF.ae_map_iff.mp hNewOnMap
    exact hTiltAC.ae_le h
  filter_upwards [hOldD, hNewAlong, hT, hTracesPosτ, hAC.ae_le hGeometry, hAC.ae_eq hTraceScaled]
    with p hDO hDN ht hp hGeom hScaled
  obtain ⟨z, rfl, _, hAmp⟩ := hGeom
  let p := chartAuxiliaryCosphere r q z
  let c : AtlasChart M := .atPoint q.center
  have hx : projection p ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  have hBase := renormalizeUnitCosphere_projection r r' p
  have hx' : projection (F p) ∈ (chartAt CoordinateSpace q.center).source := hBase.symm ▸ hx
  have hOldTensor : A.density p = chartAmplitude c (projection p) hx ((a p)⁻¹ • S p) :=
    hDO.trans (chartNormalizedIntrinsicAmplitude_of_mem r q ν hf p hx)
  have hNewTensor : pullbackAmplitudeDensity r r' A'.density p =
      chartAmplitude c (projection p) hx ((a' (F p))⁻¹ • S' (F p)) := by
    unfold pullbackAmplitudeDensity
    rw [hDN, chartNormalizedIntrinsicAmplitude_of_mem r' q ν hf (F p) hx']
    exact cast_chartAmplitude c hBase hx' hx _
  change pullbackAmplitudeDensity r r' A'.density p = (t p)⁻¹ • A.density p
  rw [hNewTensor, hOldTensor, ht, ← chartAmplitude_real_smul, hScaled, hAmp]
  exact congrArg (chartAmplitude c (projection p) hx)
    (matrix_normalized_change_trace (S p) hp.1.ne' hp.2.ne' (hsPos p).ne')

end Burnett.Microlocal.Overlap
