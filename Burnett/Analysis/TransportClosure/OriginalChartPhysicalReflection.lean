import Burnett.Analysis.TransportClosure.OriginalChartTraceReflection
import Burnett.Analysis.Microlocal.Overlap.ChartCosphereControlMeasure

/-! The scalar physical contraction preserves reflection in the original chart. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 4100000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold

open private withDensity_map_embedding from Burnett.Analysis.Microlocal.Overlap.ChartCosphereControlMeasure

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The auxiliary normalization sends the reflected round frequency to the
opposite actual covector at the same base point. -/
theorem chartAuxiliaryRay_compactChartAntipodal
    (r : Metric (M := M)) (q : CompactChartInput M) (z : Chart q.ball) :
    chartAuxiliaryRay r q (compactChartAntipodal q.ball z) = cotangentScale (-1) (chartAuxiliaryRay r q z) := by
  let c := q.center
  let y := compactChartAntipodal q.ball z
  let A := chartAuxiliaryInverse r q z.1
  let p := chartAuxiliaryRay r q y
  let p' := cotangentScale (-1) (chartAuxiliaryRay r q z)
  have hy : y.1 = z.1 := rfl
  have hBase : p.1 = p'.1 := rfl
  have hSource : p'.1 ∈ (chartAt E c).source :=
    (chartAt E c).symm_mapsTo (q.ball_in_chart z.1.property)
  have hξ : roundCovector y = fun a => (-1 : ℝ) * roundCovector z a := by
    funext a
    simp only [y, compactChartAntipodal, roundCovector, PiLp.neg_apply, neg_one_mul]
  have hScale : auxiliaryScale A (roundCovector y) = auxiliaryScale A (roundCovector z) := by
    rw [hξ, auxiliaryScale, auxiliaryScale, symbolNorm_rescale]
    norm_num
  have hCoord : cotangentCoords c p = cotangentCoords c p' := by
    change cotangentCoords c (chartAuxiliaryRay r q y) =
      cotangentCoords c (cotangentScale (-1) (chartAuxiliaryRay r q z))
    rw [cotangentScale_coords, chartAuxiliaryRay_coords, chartAuxiliaryRay_coords, hy]
    funext a
    change auxiliaryScale A (roundCovector y) * roundCovector y a =
      (-1 : ℝ) * (auxiliaryScale A (roundCovector z) * roundCovector z a)
    rw [hScale, hξ]
    ring
  calc
    _ = cotangentAssemble c (p.1, cotangentCoords c p) :=
      (cotangentAssemble_coords c p (hBase.symm ▸ hSource)).symm
    _ = cotangentAssemble c (p'.1, cotangentCoords c p') := congrArg _ (Prod.ext hBase hCoord)
    _ = _ := cotangentAssemble_coords c p' hSource

private theorem chartAuxiliaryNull_preimage_antipodal
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B) (q : CompactChartInput M) :
    compactChartAntipodal q.ball ⁻¹' chartAuxiliaryNull r B hn q = chartAuxiliaryNull r B hn q := by
  ext z
  change dualEnergy B hn (chartAuxiliaryRay r q (compactChartAntipodal q.ball z)) = 0 ↔
    dualEnergy B hn (chartAuxiliaryRay r q z) = 0
  rw [chartAuxiliaryRay_compactChartAntipodal, dualEnergy_cotangentScale]
  norm_num

/-- The actual positive quarter contraction is invariant under angular reflection. -/
theorem originalVolume_chartPhysicalJetMeasure_antipodal
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B)
    (hn : IsNondegenerate B) (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    (chartPhysicalJetMeasure r B hn q ν hf).map (compactChartAntipodal q.ball) =
      chartPhysicalJetMeasure r B hn q ν hf := by
  let φ := compactChartAntipodal q.ball
  let τ := traceMeasure ν
  let Z := chartAuxiliaryNull r B hn q
  let D := chartPhysicalJetContraction r B q ν hf
  let w (z : Chart q.ball) := ENNReal.ofReal (D z).re
  have hE : MeasurableEmbedding φ := (compactChartAntipodalHomeomorph q.ball).measurableEmbedding
  obtain ⟨hMP, hEntry⟩ := originalVolume_chartTrace_and_density_antipodal B g hB hg hn q σ ν hf hRep
  have hConj : ∀ᵐ z ∂τ, D (φ z) = conj (D z) := by
    filter_upwards [hEntry] with z hz
    have hBase : (φ z).1 = z.1 := rfl
    have hz' (i j : JetSlot) : density ν hf (φ z) i j = conj (density ν hf z i j) := hz i j
    simp only [D, chartPhysicalJetContraction, hBase, map_sum, map_mul, Complex.conj_ofReal, hz']
  have hZ := measurableSet_chartAuxiliaryNull r B hB hs hn q
  have hInvZ : φ ⁻¹' Z = Z := chartAuxiliaryNull_preimage_antipodal r B hn q
  have hMap : (τ.restrict Z).map φ = τ.restrict Z := by
    calc
      _ = (τ.map φ).restrict Z := by rw [Measure.restrict_map hE.measurable hZ, hInvZ]
      _ = _ := congrArg (fun μ => μ.restrict Z) hMP.map_eq
  have hW : w =ᵐ[τ.restrict Z] w ∘ φ := by
    filter_upwards [ae_restrict_of_ae hConj] with z hz
    simp only [w, comp_apply, hz, Complex.conj_re]
  change ((τ.restrict Z).withDensity w).map φ = (τ.restrict Z).withDensity w
  calc
    _ = ((τ.restrict Z).withDensity (w ∘ φ)).map φ := congrArg (Measure.map φ) (withDensity_congr_ae hW)
    _ = ((τ.restrict Z).map φ).withDensity w := (withDensity_map_embedding hE _ _).symm
    _ = _ := congrArg (fun m => m.withDensity w) hMap

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The normalized original physical chart measure is invariant under the
actual negative radial map, including the original cutoff weighting. -/
theorem originalVolume_normalizedCotangentPhysicalMeasure_antipodal
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B)
    (hn : IsNondegenerate B) (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    (normalizedCotangentPhysicalMeasure q r B hn ν hf).map (cotangentScale (-1)) =
      normalizedCotangentPhysicalMeasure q r B hn ν hf := by
  let φ := compactChartAntipodal q.ball
  let f := chartAuxiliaryRay r q
  let μ := chartPhysicalJetMeasure r B hn q ν hf
  let w := chartInverseCutoffSquare q
  have hE : MeasurableEmbedding φ := (compactChartAntipodalHomeomorph q.ball).measurableEmbedding
  have hφ : μ.map φ = μ := originalVolume_chartPhysicalJetMeasure_antipodal r B g hB hg hs hn q σ ν hf hRep
  have hW : w ∘ φ = w := rfl
  have hInvar : (μ.withDensity w).map φ = μ.withDensity w := by
    calc
      _ = (μ.map φ).withDensity w := by rw [withDensity_map_embedding hE, hW]
      _ = _ := congrArg (fun m => m.withDensity w) hφ
  have hscale : Measurable (cotangentScale (-1) : CotangentBundle M → CotangentBundle M) :=
    (continuous_cotangentScale.comp (continuous_const.prodMk continuous_id)).measurable
  have hfM := (continuous_chartAuxiliaryRay r q).measurable
  have hEq : cotangentScale (-1) ∘ f = f ∘ φ := funext fun z => (chartAuxiliaryRay_compactChartAntipodal r q z).symm
  change ((μ.withDensity w).map f).map (cotangentScale (-1)) = (μ.withDensity w).map f
  rw [Measure.map_map hscale hfM, hEq, ← Measure.map_map hfM hE.measurable, hInvar]

end Burnett.Microlocal.Overlap
