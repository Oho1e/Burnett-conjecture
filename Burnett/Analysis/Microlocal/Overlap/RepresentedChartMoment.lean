import Burnett.Analysis.Microlocal.Overlap.RepresentedChartRicci
import Burnett.Analysis.Microlocal.RicciDensityNullMoment
import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalJetMeasure

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ManifoldMetricSequence BackgroundConnection CurvatureDifference
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryInverse chartAuxiliaryNorm_pos)
open Burnett.F05.ActualCoordinateRicciDensity (backgroundInverse_symmetric)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (ae_originalVolume_auxiliaryAmplitude chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector auxiliaryUnitCovector_unit
  chartPhysicalCovariance roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.RawCovariance
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.X02.SobolevTestJet (D Space)
open scoped BigOperators ContDiff Topology Manifold ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The original coordinate Ricci component is the second moment of the
same positive null measure used in the overlap construction. -/
theorem original_chartRicci_eq_physical_secondMoment
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (ψ : D) (hψ : tsupport (ψ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0})
    (b d : Index) :
    let ξ (p : Chart q.ball) := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
    (∫ x, (ψ : Space → ℝ) x * coordinateRicci (computedConnection (coordinateBilinear B q.center)) x b d
        ∂ManifoldVolume.coordinateMeasure B q.center) =
    ∫ p, ((ψ : Space → ℝ) p.1 * ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) * (ξ p b * ξ p d)
      ∂chartPhysicalJetMeasure r B hSig.isNondegenerate q ν hf := by
  intro ξ
  let τ := traceMeasure ν
  let Z := chartAuxiliaryNull r B hSig.isNondegenerate q
  let D₀ := chartPhysicalJetContraction r B q ν hf
  let G (p : Chart q.ball) := backgroundInverse B q.center p.1
  let f (p : Chart q.ball) :=
    ((ψ : Space → ℝ) p.1 * ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) * (ξ p b * ξ p d)
  have hZ : MeasurableSet Z := measurableSet_chartAuxiliaryNull r B hB hSig.isSymmetric hSig.isNondegenerate q
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hf hRep
  have hRaw := original_Ricci_eq_normalized_jetContraction r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hf hRep ψ hψ b d
  rw [hRaw]
  have hPoint : ∀ᵐ p ∂τ, (∑ i : JetSlot, ∑ j : JetSlot,
      (((ψ : Space → ℝ) p.1 * rawJetProductCoefficient (G p) b d i j) *
        ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) * (density ν hf p i j).re) =
      Z.indicator (fun p => f p * (D₀ p).re) p := by
    filter_upwards [hData] with p hp
    obtain ⟨hA, hEntry, _, hKer⟩ := hp
    let A := chartAuxiliaryAmplitude r q ν hf p
    have hOne : symbolNorm (chartAuxiliaryInverse r q p.1) (ξ p) = 1 :=
      auxiliaryUnitCovector_unit _ _ (chartAuxiliaryNorm_pos r q p)
    have hξ : ξ p ≠ 0 := by
      intro hzero
      simp only [hzero, symbolNorm, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_ne_one] at hOne
    have hFact (i j : JetSlot) : density ν hf p i j =
        (ξ p i.1 : ℂ) * (ξ p j.1 : ℂ) * A j.2 i.2 := by
      have h := hEntry j i
      change density ν hf p i j = (ξ p j.1 : ℂ) * (ξ p i.1 : ℂ) * A j.2 i.2 at h
      rw [mul_comm (ξ p i.1 : ℂ)]
      exact h
    have hAlgebra := rawJetContraction_eq_nullMoment_of_factored (G p) (ξ p) A (density ν hf p)
      (backgroundInverse_symmetric B hSig.isSymmetric hSig.isNondegenerate q p.1) hξ hA hFact hKer b d
    have hPhysical : D₀ p = (1 / 4 : ℂ) *
        Burnett.Microlocal.PhysicalDensity.physicalContraction (G p) A :=
      chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r B q ν hf p hEntry
    rw [← hPhysical] at hAlgebra
    let w := (ψ : Space → ℝ) p.1 * ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹
    have hWeight : (∑ i : JetSlot, ∑ j : JetSlot,
        (((ψ : Space → ℝ) p.1 * rawJetProductCoefficient (G p) b d i j) *
          ((q.cutoff : Space → ℝ) p.1 ^ 2)⁻¹) * (density ν hf p i j).re) =
        w * ∑ i : JetSlot, ∑ j : JetSlot, rawJetProductCoefficient (G p) b d i j *
          (density ν hf p i j).re := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [w]
      ring
    rw [hWeight, hAlgebra]
    have hNull : p ∈ Z ↔ symbolNorm (G p) (ξ p) = 0 :=
      chartAuxiliaryNull_iff_symbolNorm_eq_zero r B hSig.isSymmetric hSig.isNondegenerate q p
    by_cases hp : p ∈ Z
    · rw [indicator_of_mem hp, if_pos (hNull.mp hp)]
      exact (mul_assoc w _ _).symm
    · rw [indicator_of_notMem hp, if_neg (fun h => hp (hNull.mpr h)), mul_zero]
  refine (integral_congr_ae hPoint).trans ?_
  rw [integral_indicator hZ]
  let μ := τ.restrict Z
  have hInt : Integrable D₀ μ :=
    (integrable_chartPhysicalJetContraction r B hB hSig.isNondegenerate q ν hf).mono_measure
      Measure.restrict_le_self
  have hNonneg : ∀ᵐ p ∂μ, 0 ≤ (D₀ p).re :=
    (ae_original_chartPhysicalJetContraction_nonneg_real r B g hB hg hSig hsG hnG hconv hb hv
      q σ hσ ν hf hRep).mono fun _ hp => hp.1
  change (∫ p, f p * (D₀ p).re ∂μ) = ∫ p, f p ∂positiveMeasureOfComplexDensity μ D₀
  have hMeas : AEMeasurable (fun p => ENNReal.ofReal (D₀ p).re) μ :=
    (Complex.reCLM.integrable_comp hInt).aemeasurable.ennreal_ofReal
  rw [positiveMeasureOfComplexDensity, integral_withDensity_eq_integral_toReal_smul₀ hMeas]
  · apply integral_congr_ae
    filter_upwards [hNonneg] with p hp
    rw [ENNReal.toReal_ofReal hp, smul_eq_mul, mul_comm]
  · exact Eventually.of_forall (fun p => ENNReal.ofReal_lt_top)

end Burnett.Microlocal.Overlap
