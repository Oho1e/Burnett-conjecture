import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Burnett.Analysis.Microlocal.OriginalRationalPairingLimits

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ContDiff ENNReal Topology Manifold

/-- Every continuous spatial multiplier and rational angular multiplier is represented
on the given subsequence by the indicated ordered component of the chart density. -/
theorem RepresentsCompactJetPairings.tendsto_rational
    {K : BallData} {w : ℕ → JetSlot → ComplexL2 Space} {σ : ℕ → ℕ}
    {ν : (JetSlot → ℂ) → Measure (Chart K)} {hfin : ∀ v, IsFiniteMeasure (ν v)}
    (hRep : RepresentsCompactJetPairings K w σ ν hfin)
    (a : BoundedSymbol Space) (ha : Continuous (a : Space → ℂ))
    (p : RationalPolynomial × RationalPolynomial) (k l : JetSlot) :
    Tendsto (fun n => inner ℂ (w (σ n) l)
      (symbolCLM a (fourierMultiplier (complexRationalAngularSymbol p) (w (σ n) k))))
      atTop (𝓝 (∫ x, a (x.1 : Space) * complexRationalAngularSymbol p (x.2 : Space) *
        density ν hfin x l k ∂traceMeasure ν)) := by
  let b := complexRationalAngularSymbol p
  have hs : ContDiffOn ℝ ∞ (b : Space → ℂ) ({0}ᶜ : Set Space) := complexRationalAngular_contDiffOn p
  have hd : DegreeZero (b : Space → ℂ) := complexRationalAngular_degreeZero p
  let ar := fun _ : Unit => a
  let br := fun _ : Unit => b
  obtain ⟨_, _, _, _, _, _, hAll⟩ := hRep
  have hr := hAll Unit ar br (fun _ => ha) (fun _ => hs) (fun _ => hd) l k
  have hop (v : ComplexL2 Space) : finiteSeparableOperator ar br v =
      symbolCLM a (fourierMultiplier b v) := by
    simp [finiteSeparableOperator, ar, br, separableOperator]
  have hsym (x : Chart K) : finiteSmoothRestriction K ar br (fun _ => ha) (fun _ => hs) x =
      a (x.1 : Space) * b (x.2 : Space) := by
    rcases x with ⟨x, ξ⟩
    rw [finiteSmoothRestriction_apply]
    simp [ar, br]
  simpa only [hop, hsym] using hr

/-- A limit on an earlier subsequence equals the matrix measure integral on its refinement. -/
theorem RepresentsCompactJetPairings.eq_integral_of_rational_limit
    {K : BallData} {w : ℕ → JetSlot → ComplexL2 Space} {σ τ : ℕ → ℕ}
    {ν : (JetSlot → ℂ) → Measure (Chart K)} {hfin : ∀ v, IsFiniteMeasure (ν v)}
    (hRep : RepresentsCompactJetPairings K w (σ ∘ τ) ν hfin) (hτ : StrictMono τ)
    (a : BoundedSymbol Space) (ha : Continuous (a : Space → ℂ))
    (p : RationalPolynomial × RationalPolynomial) (k l : JetSlot) {z : ℂ}
    (hL : Tendsto (fun n => inner ℂ (w (σ n) l)
      (symbolCLM a (fourierMultiplier (complexRationalAngularSymbol p) (w (σ n) k)))) atTop (𝓝 z)) :
    z = ∫ x, a (x.1 : Space) * complexRationalAngularSymbol p (x.2 : Space) *
      density ν hfin x l k ∂traceMeasure ν :=
  tendsto_nhds_unique (hL.comp hτ.tendsto_atTop) (hRep.tendsto_rational a ha p k l)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Numerical limits of the original volume-weighted components, first chosen on one
common subsequence, are represented by the positive jet matrix measure on a refinement.
The original subsequence's limits and multiplier bounds remain part of the conclusion. -/
theorem exists_originalVolume_measures_realizing_rational_limits
    {I J : Type*} [Countable I] [Countable J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (charts : I → CompactChartInput M) :
    ∃ C : I → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ a : I → J → BoundedSymbol Space,
      (∀ i j, Continuous (a i j : Space → ℂ)) →
      ∃ σ τ : ℕ → ℕ, StrictMono σ ∧ StrictMono τ ∧ ∀ i,
        let q := charts i
        let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)
        ∃ L : J → (RationalPolynomial × RationalPolynomial) → JetSlot → JetSlot → ℂ,
        ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
          RepresentsCompactJetPairings q.ball w (σ ∘ τ) ν hfin ∧
          ∀ j p k l,
            ‖L j p k l‖ ≤ ((a i j).bound * (complexRationalAngularSymbol p).bound) * C i ^ 2 ∧
            Tendsto (fun n => inner ℂ (w (σ n) l)
              (symbolCLM (a i j) (fourierMultiplier (complexRationalAngularSymbol p) (w (σ n) k))))
              atTop (𝓝 (L j p k l)) ∧
            L j p k l = ∫ x, a i j (x.1 : Space) * complexRationalAngularSymbol p (x.2 : Space) *
              density ν hfin x l k ∂traceMeasure ν := by
  obtain ⟨C, hC, hNumerical⟩ :=
    exists_countable_originalVolume_rational_pairing_limits (J := J) r B g hB hg hn hconv hb charts
  refine ⟨C, hC, fun a ha => ?_⟩
  obtain ⟨σ, hσ, hCharts⟩ := hNumerical a
  obtain ⟨τ, hτ, hMeasures⟩ :=
    exists_countable_originalVolume_matrixDensities r B g hB hg hn hconv hb charts σ hσ
  refine ⟨σ, τ, hσ, hτ, fun i => ?_⟩
  obtain ⟨L, hL, hLimits⟩ := hCharts i
  obtain ⟨ν, hfin, hRep⟩ := hMeasures i
  refine ⟨L, ν, hfin, hRep, fun j p k l => ⟨hL j p k l, hLimits j p k l, ?_⟩⟩
  exact hRep.eq_integral_of_rational_limit hτ (a i j) (ha i j) p k l (hLimits j p k l)

end Burnett.Microlocal.CountableAuxiliaryCharts
