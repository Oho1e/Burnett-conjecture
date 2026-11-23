import Burnett.Analysis.Compactness.DiagonalSubsequence
import Burnett.Analysis.Microlocal.CompactJetSmoothPairings
import Burnett.Analysis.Microlocal.OriginalGradientInputs
import Burnett.Analysis.Microlocal.VolumeWeightedChartJet

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.OriginalCoordinateCurl Burnett.F05.CoordinateCurl
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped ContDiff ENNReal Topology Manifold Matrix ComplexOrder

/-- The polarized entries of this chart measure and its trace density represent every
finite smooth separated test of the same ordered coordinate derivatives. -/
def RepresentsCompactJetPairings (K : BallData) (w : ℕ → JetSlot → ComplexL2 Space)
    (σ : ℕ → ℕ) (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v)) : Prop :=
  (∀ v, (ν v).Regular) ∧ IsFiniteMeasure (traceMeasure ν) ∧
  (∀ s : Set (Chart K), MeasurableSet s →
    Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix JetSlot JetSlot ℂ)) ∧
  (∀ i j, entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure) ∧
  (∀ s : Set (Chart K), MeasurableSet s → ∀ i j,
    (∫ x in s, density ν hfin x i j ∂traceMeasure ν) = entryMeasure ν hfin i j s) ∧
  (∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef ∧ Matrix.trace (density ν hfin x) = 1) ∧
  ∀ (J : Type) [Fintype J] (a m : J → BoundedSymbol Space)
      (ha : ∀ j, Continuous (a j : Space → ℂ))
      (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
      (_ : ∀ j, DegreeZero (m j : Space → ℂ)) (i j : JetSlot),
    Tendsto (fun n => inner ℂ (w (σ n) i) (finiteSeparableOperator a m (w (σ n) j)))
      atTop (𝓝 (∫ x, finiteSmoothRestriction K a m ha hm x * density ν hfin x i j ∂traceMeasure ν))

private theorem RepresentsCompactJetPairings.of_tail
    {K : BallData} {w : ℕ → JetSlot → ComplexL2 Space} {σ τ ρ : ℕ → ℕ} (t : ℕ) (hρ : StrictMono ρ)
    (hTail : ∀ n, σ (n + t) = τ (ρ n)) {ν : (JetSlot → ℂ) → Measure (Chart K)}
    {hfin : ∀ v, IsFiniteMeasure (ν v)} (h : RepresentsCompactJetPairings K w τ ν hfin) :
    RepresentsCompactJetPairings K w σ ν hfin := by
  obtain ⟨hReg, hFinite, hPSD, hAC, hSet, hD, hLim⟩ := h
  refine ⟨hReg, hFinite, hPSD, hAC, hSet, hD, ?_⟩
  intro J _ a m ha hm hd i j
  exact tendsto_of_strictSubsequence_tail
    (fun n => inner ℂ (w n i) (finiteSeparableOperator a m (w n j))) _ σ τ ρ t hρ hTail
    (hLim J a m ha hm hd i j)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

private theorem exists_originalVolume_matrixDensity_on_subsequence
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        RepresentsCompactJetPairings q.ball (originalGradient_volumeWeightedL2
          B g hB hg hn q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart)) (s ∘ τ) ν hfin := by
  let q' := volumeModeInput B hB hn q
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport q'.cutoff
  obtain ⟨f, hf, hLp, η, hη, C, _, hBound, hWeak, _, hSupp, hOriginal, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r B g hB hg hn hconv hb q'.center q'.cutoff
      (q'.cutoff_support.trans q'.ball_in_chart) θ hθ
  have hK (n : ℕ) (i : JetSlot) (x : Space) (hx : f n i x ≠ 0) : x ∈ q.ball.closedBall :=
    q'.cutoff_support (hSupp n i (subset_tsupport (f n i) hx))
  obtain ⟨τ, hτ, ν, hfin, hReg, hTrace, hPSD, hAC, hSet, hDensity, hAll⟩ :=
    exists_compactChartMatrixDensity_allFiniteSmoothPairings q.ball
      (fun n => f (s n)) (fun n => hf (s n)) (fun n => hLp (s n)) η
      (fun n => hη (s n)) (fun n => hK (s n)) C (fun n => hBound (s n))
      (fun i φ => (hWeak i φ).comp hs.tendsto_atTop)
  have hInput (n : ℕ) (i : JetSlot) :
      (sourceSchwartz (hf n i) η (hη n i)).toLp 2 volume =
        originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart) n i :=
    congrArg (fun f : SchwartzMap Space ℂ => f.toLp 2 volume) (congrFun (hOriginal n) i)
  refine ⟨τ, hτ, ν, hfin, hReg, hTrace, hPSD, hAC, hSet, hDensity, ?_⟩
  intro J _ a m ha hm hd i j
  simpa only [hInput, Function.comp_apply] using hAll J a m ha hm hd i j

/-- One further strict subsequence of any fixed original metric subsequence gives a
positive matrix measure for every prescribed chart. All smooth separated tests and both
ordered jet slots use that same subsequence and the same chart measure. -/
theorem exists_countable_originalVolume_matrixDensities {I : Type*} [Countable I]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (charts : I → CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ i,
      let q := charts i
      let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)
      ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        RepresentsCompactJetPairings q.ball w (s ∘ τ) ν hfin := by
  let P (i : I) (t : ℕ → ℕ) :=
    ∃ ν : (JetSlot → ℂ) → Measure (Chart (charts i).ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
      RepresentsCompactJetPairings (charts i).ball (originalGradient_volumeWeightedL2 B g hB hg hn
        (charts i).center (charts i).cutoff ((charts i).cutoff_support.trans (charts i).ball_in_chart))
        (s ∘ t) ν hfin
  have step (i : I) (t : ℕ → ℕ) (ht : StrictMono t) :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (t ∘ ψ) :=
    exists_originalVolume_matrixDensity_on_subsequence r B g hB hg hn hconv hb (charts i)
      (s ∘ t) (hs.comp ht)
  obtain ⟨τ, hτ, hTails⟩ := exists_diagonal_with_countable_tails P step
  refine ⟨τ, hτ, fun i => ?_⟩
  obtain ⟨t, σ, ρ, _, hρ, ⟨ν, hfin, hRep⟩, hTail⟩ := hTails i
  have hComposed : ∀ n, (s ∘ τ) (n + t) = (s ∘ σ) (ρ n) := fun n => congrArg s (hTail n)
  exact ⟨ν, hfin, RepresentsCompactJetPairings.of_tail
    (σ := s ∘ τ) (τ := s ∘ σ) (ρ := ρ) t hρ hComposed hRep⟩

end Burnett.Microlocal.CountableAuxiliaryCharts
