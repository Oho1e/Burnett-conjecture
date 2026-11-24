import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalJetMeasure

/-! Change the auxiliary metric on the same represented original chart. -/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle dualEnergy dualEnergy_chart)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
  (chartAuxiliaryAmplitude ae_originalVolume_auxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity
  (auxiliaryScale auxiliaryScale_pos auxiliaryUnitCovector roundCovector
    symbolNorm_rescale)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.PhysicalDensity (physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem chartAuxiliaryRay_dualEnergy_rescale (r : Metric (M := M)) (B : Field (M := M))
    (hsB : IsSymmetric B) (hnB : IsNondegenerate B) (q : CompactChartInput M) (p : Chart q.ball) :
    dualEnergy B hnB (chartAuxiliaryRay r q p) =
      (auxiliaryScale (chartAuxiliaryInverse r q p.1) (roundCovector p)) ^ 2 *
        symbolNorm (backgroundInverse B q.center p.1) (roundCovector p) := by
  let e := chartAt CoordinateSpace q.center
  have hp := q.ball_in_chart p.1.property
  have hx : (chartAuxiliaryRay r q p).1 ∈ e.source := e.symm_mapsTo hp
  rw [dualEnergy_chart B hnB hsB q.center (chartAuxiliaryRay r q p) hx, chartAuxiliaryRay_coords]
  change symbolNorm (backgroundInverse B q.center (e (e.symm p.1)))
    (auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)) = _
  rw [e.right_inv hp]
  exact symbolNorm_rescale (backgroundInverse B q.center p.1) (roundCovector p)
    (auxiliaryScale (chartAuxiliaryInverse r q p.1) (roundCovector p))

/-- The old normalized ray has squared new norm equal to the ratio of the
two squared norms of the very same round covector. -/
theorem chartAuxiliaryRay_changeWeight_eq_ratio (r r' : Metric (M := M))
    (q : CompactChartInput M) (p : Chart q.ball) :
    dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') (chartAuxiliaryRay r q p) =
      symbolNorm (chartAuxiliaryInverse r' q p.1) (roundCovector p) /
        symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) := by
  rw [chartAuxiliaryRay_dualEnergy_rescale r r'.inner r'.symm
    (GlobalLeviCivita.inner_nondegenerate r') q p, auxiliaryScale, inv_pow,
    Real.sq_sqrt (chartAuxiliaryNorm_pos r q p).le]
  change (symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p))⁻¹ *
      symbolNorm (chartAuxiliaryInverse r' q p.1) (roundCovector p) = _
  rw [div_eq_mul_inv, mul_comm]

/-- The two actual null shells have the same preimage on the fixed round chart. -/
theorem chartAuxiliaryNull_changeAuxiliary (r r' : Metric (M := M)) (B : Field (M := M))
    (hsB : IsSymmetric B) (hnB : IsNondegenerate B) (q : CompactChartInput M) :
    chartAuxiliaryNull r' B hnB q = chartAuxiliaryNull r B hnB q := by
  ext p
  have hNull (u : Metric (M := M)) : p ∈ chartAuxiliaryNull u B hnB q ↔
      symbolNorm (backgroundInverse B q.center p.1) (roundCovector p) = 0 := by
    change dualEnergy B hnB (chartAuxiliaryRay u q p) = 0 ↔ _
    rw [chartAuxiliaryRay_dualEnergy_rescale u B hsB hnB q p, mul_eq_zero]
    exact or_iff_right (pow_ne_zero 2 (auxiliaryScale_pos _ _ (chartAuxiliaryNorm_pos u q p)).ne')
  exact (hNull r').trans (hNull r).symm

private theorem quarterContraction_smul (G : Tensor2) (c : ℂ) (A : Matrix Pair Pair ℂ) :
    (1 / 4 : ℂ) * physicalContraction G (c • A) =
      c * ((1 / 4 : ℂ) * physicalContraction G A) := by
  have h : physicalContraction G (c • A) = c * physicalContraction G A := by
    simp only [physicalContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [h]
  ring

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Both physical contractions use the same round amplitude of the same original
gradient witness. The factor is the squared new norm at the old unit ray. -/
theorem ae_original_chartPhysicalJetContraction_changeAuxiliary
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ p ∂traceMeasure ν,
      let w := dualEnergy r'.inner (GlobalLeviCivita.inner_nondegenerate r') (chartAuxiliaryRay r q p)
      chartPhysicalJetContraction r' B q ν hfin p =
        (w : ℂ) * chartPhysicalJetContraction r B q ν hfin p := by
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  have hData := ae_originalVolume_auxiliaryAmplitude r B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv hb hv q σ hσ ν hfin hRep
  have hData' := ae_originalVolume_auxiliaryAmplitude r' B g hB hg hSig.isSymmetric hsG
    hSig.isNondegenerate hnG hconv' hb' hv q σ hσ ν hfin hRep
  filter_upwards [hData, hData'] with p hA hA'
  have hR : chartPhysicalJetContraction r B q ν hfin p = _ :=
    chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r B q ν hfin p hA.2.1
  have hR' : chartPhysicalJetContraction r' B q ν hfin p = _ :=
    chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r' B q ν hfin p hA'.2.1
  rw [hA.2.2.1, quarterContraction_smul] at hR
  rw [hA'.2.2.1, quarterContraction_smul] at hR'
  dsimp only
  rw [hR, hR', chartAuxiliaryRay_changeWeight_eq_ratio]
  let a := symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p)
  let b := symbolNorm (chartAuxiliaryInverse r' q p.1) (roundCovector p)
  have hProd : ((b / a : ℝ) : ℂ) * (a : ℂ) = (b : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (chartAuxiliaryNorm_pos r q p).ne']
  rw [← mul_assoc ((b / a : ℝ) : ℂ) (a : ℂ), hProd]

end Burnett.Microlocal.Overlap
