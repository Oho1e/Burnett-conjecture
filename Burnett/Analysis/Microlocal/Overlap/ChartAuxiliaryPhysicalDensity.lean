import Burnett.Analysis.Microlocal.Overlap.FactoredPhysicalJetDensity
import Burnett.Analysis.Microlocal.OriginalVolumeAuxiliaryAmplitude

/-! Identify the chart jet contraction with the same auxiliary amplitude. -/

set_option autoImplicit false
set_option maxHeartbeats 260000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Matrix MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Geometry.UnitNullCompactness (cotangentCoords dualEnergy dualEnergy_chart)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity
  (auxiliaryUnitCovector auxiliaryUnitCovector_unit chartPhysicalCovariance roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.PhysicalDensity (physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped BigOperators ComplexOrder ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- On the actual bundle ray, vanishing of the dual energy is the coordinate
Ricci-symbol null condition at its auxiliary-unit representative. -/
theorem chartAuxiliaryNull_iff_symbolNorm_eq_zero (r : Metric (M := M)) (B : Field (M := M))
    (hsB : IsSymmetric B) (hnB : IsNondegenerate B) (q : CompactChartInput M)
    (p : Chart q.ball) :
    p ∈ chartAuxiliaryNull r B hnB q ↔
      symbolNorm (backgroundInverse B q.center p.1)
        (auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)) = 0 := by
  let e := chartAt CoordinateSpace q.center
  have hp := q.ball_in_chart p.1.property
  have hx : (chartAuxiliaryRay r q p).1 ∈ e.source := e.symm_mapsTo hp
  change dualEnergy B hnB (chartAuxiliaryRay r q p) = 0 ↔ _
  rw [dualEnergy_chart B hnB hsB q.center (chartAuxiliaryRay r q p) hx, chartAuxiliaryRay_coords]
  change symbolNorm (backgroundInverse B q.center (e (e.symm p.1)))
    (auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)) = 0 ↔ _
  rw [e.right_inv hp]

/-- Contracting the original jet density with the actual inverse metrics gives
one quarter of the physical contraction of its auxiliary-unit amplitude. -/
theorem chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (p : Chart q.ball)
    (hEntry : let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
      ∀ i j : JetSlot, chartPhysicalCovariance q.ball ν hfin p i j =
        (η i.1 : ℂ) * (η j.1 : ℂ) * chartAuxiliaryAmplitude r q ν hfin p i.2 j.2) :
    (∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B q.center p.1 i j : ℂ) *
      density ν hfin p i j) =
      (1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center p.1)
        (chartAuxiliaryAmplitude r q ν hfin p) := by
  let R := chartAuxiliaryInverse r q p.1
  let η := auxiliaryUnitCovector R (roundCovector p)
  have hR : backgroundInverse r.inner q.center p.1 = R := rfl
  have hUnit : symbolNorm R η = 1 :=
    auxiliaryUnitCovector_unit R (roundCovector p) (chartAuxiliaryNorm_pos r q p)
  unfold chartPhysicalJetWeight
  rw [hR]
  exact orderedPhysicalJetWeight_factored R (backgroundInverse B q.center p.1) η
    (density ν hfin p) (chartAuxiliaryAmplitude r q ν hfin p) hUnit hEntry

theorem chartPhysicalJetWeight_contraction_nonneg_real
    (r : Metric (M := M)) (B : Field (M := M)) (hsB : IsSymmetric B)
    (hnB : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (p : Chart q.ball) (hp : p ∈ chartAuxiliaryNull r B hnB q)
    (frame : TensorFrame.LorentzFrame (backgroundInverse B q.center p.1))
    (hPS : (chartAuxiliaryAmplitude r q ν hfin p).PosSemidef)
    (hEntry : let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
      ∀ i j : JetSlot, chartPhysicalCovariance q.ball ν hfin p i j =
        (η i.1 : ℂ) * (η j.1 : ℂ) * chartAuxiliaryAmplitude r q ν hfin p i.2 j.2)
    (hK : let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
      ∀ v : Pair → ℂ, let k (a b : Index) := (chartAuxiliaryAmplitude r q ν hfin p *ᵥ v) (a, b)
        IsSymmetricComplexTensor k ∧
          ∀ a b, complexRicciSymbol (backgroundInverse B q.center p.1) η k a b = 0) :
    let D := ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B q.center p.1 i j : ℂ) *
      density ν hfin p i j
    0 ≤ D.re ∧ D.im = 0 := by
  dsimp only
  let R := chartAuxiliaryInverse r q p.1
  let η := auxiliaryUnitCovector R (roundCovector p)
  let G := backgroundInverse B q.center p.1
  let S := chartAuxiliaryAmplitude r q ν hfin p
  have hUnit : symbolNorm R η = 1 :=
    auxiliaryUnitCovector_unit R (roundCovector p) (chartAuxiliaryNorm_pos r q p)
  have hη : η ≠ 0 := by
    intro hz
    simp only [hz, symbolNorm, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_ne_one] at hUnit
  have hNull : symbolNorm G η = 0 := (chartAuxiliaryNull_iff_symbolNorm_eq_zero r B hsB hnB q p).mp hp
  have hPos := physicalContraction_of_null_amplitude G frame η hη hNull S hPS hK
  rw [chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude r B q ν hfin p hEntry]
  have hQuarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hQuarter]
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hPos.1
  · change (((1 / 4 : ℝ) : ℂ) * physicalContraction G S).im = 0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hPos.2, mul_zero, zero_mul, add_zero]

/-- The real nonnegativity uses the same trace and the actual Borel null
restriction, with the amplitude range constraint on a trace-conull set. -/
theorem ae_chartPhysicalJetWeight_contraction_nonneg_real
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hsB : IsSymmetric B)
    (hnB : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hFrame : ∀ y : q.ball.Point, Nonempty (TensorFrame.LorentzFrame (backgroundInverse B q.center y)))
    (hData : ∀ᵐ p ∂traceMeasure ν,
      let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
      let S := chartAuxiliaryAmplitude r q ν hfin p
      S.PosSemidef ∧
      (∀ i j : JetSlot, chartPhysicalCovariance q.ball ν hfin p i j =
        (η i.1 : ℂ) * (η j.1 : ℂ) * S i.2 j.2) ∧
      ∀ v : Pair → ℂ, let k (a b : Index) := (S *ᵥ v) (a, b)
        IsSymmetricComplexTensor k ∧
          ∀ a b, complexRicciSymbol (backgroundInverse B q.center p.1) η k a b = 0) :
    ∀ᵐ p ∂(traceMeasure ν).restrict (chartAuxiliaryNull r B hnB q),
      let D := ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B q.center p.1 i j : ℂ) *
        density ν hfin p i j
      0 ≤ D.re ∧ D.im = 0 := by
  filter_upwards [ae_restrict_mem (measurableSet_chartAuxiliaryNull r B hB hsB hnB q),
    ae_restrict_of_ae hData] with p hp hA
  obtain ⟨frame⟩ := hFrame p.1
  obtain ⟨hPS, hEntry, hK⟩ := hA
  exact chartPhysicalJetWeight_contraction_nonneg_real r B hsB hnB q ν hfin p hp frame hPS hEntry hK

end Burnett.Microlocal.Overlap
