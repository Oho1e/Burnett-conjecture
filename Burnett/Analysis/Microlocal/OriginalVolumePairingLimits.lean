import Burnett.Analysis.Compactness.DiagonalSubsequence
import Burnett.Analysis.Compactness.OrderedPairings
import Burnett.Analysis.Microlocal.OriginalGradientInputs
import Burnett.Analysis.Microlocal.VolumeWeightedChartJet

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.OriginalCoordinateCurl Burnett.F05.CoordinateCurl
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SeparablePositive
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (Space)
open scoped ContDiff ENNReal Topology Manifold ComplexConjugate

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- All volume-weighted coordinate derivatives of the original metrics share a bound on
each given compact chart. The constant is chosen before the sequence index and tensor slot. -/
theorem exists_originalVolumeJet_uniform_bound
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (i : JetSlot),
      ‖originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart) n i‖ ≤ C := by
  let v := volumeModeInput B hB hn q
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport v.cutoff
  obtain ⟨f, hs, hf, η, hη, C, hC, hBound, _, _, _, hSchw, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r B g hB hg hn hconv hb v.center v.cutoff
      (v.cutoff_support.trans v.ball_in_chart) θ hθ
  refine ⟨C, hC, fun n i => ?_⟩
  change ‖(originalGradientSchwartz B g hB hg v.center v.cutoff
    (v.cutoff_support.trans v.ball_in_chart) n i).toLp 2 volume‖ ≤ C
  rw [← congrFun (hSchw n) i]
  refine (Lp.norm_le_norm_of_ae_le (g := (hf n i).toLp (f n i)) ?_).trans (hBound n i)
  filter_upwards [(sourceSchwartz (hs n i) η (hη n i)).coeFn_toLp 2 volume,
    (hf n i).coeFn_toLp] with x hx hy
  rw [hx, hy]
  change ‖((f n i x : ℝ) : ℂ)‖ ≤ ‖f n i x‖
  simp

/-- A countable family of prescribed charts and countably many bounded tests on each chart
admit one subsequence of the original metrics for all ordered volume-weighted jet pairings.
The tested operator acts in the second, complex-linear slot. -/
theorem exists_countable_originalVolume_pairing_limits {I J : Type*} [Countable I] [Countable J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (charts : I → CompactChartInput M) :
    ∃ C : I → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ T : I → J → ComplexL2 Space →L[ℂ] ComplexL2 Space,
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i,
          let q := charts i
          let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
            (q.cutoff_support.trans q.ball_in_chart)
          ∃ L : J → JetSlot → JetSlot → ℂ,
            (∀ j k l, ‖L j k l‖ ≤ ‖T i j‖ * C i ^ 2) ∧
            ∀ j k l, Tendsto (fun n => inner ℂ (w (σ n) l) (T i j (w (σ n) k)))
              atTop (𝓝 (L j k l)) := by
  classical
  let u (i : I) := originalGradient_volumeWeightedL2 B g hB hg hn (charts i).center
    (charts i).cutoff ((charts i).cutoff_support.trans (charts i).ball_in_chart)
  choose C hC hU using fun i => exists_originalVolumeJet_uniform_bound r B g hB hg hn hconv hb (charts i)
  refine ⟨C, hC, fun T => ?_⟩
  let P (i : I) (s : ℕ → ℕ) := ∃ L : J → JetSlot → JetSlot → ℂ,
    (∀ j k l, ‖L j k l‖ ≤ ‖T i j‖ * C i ^ 2) ∧
    ∀ j k l, Tendsto (fun n => inner ℂ (u i (s n) l) (T i j (u i (s n) k)))
      atTop (𝓝 (L j k l))
  have step (i : I) (s : ℕ → ℕ) (_hs : StrictMono s) :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (s ∘ ψ) := by
    obtain ⟨ψ, hψ, A, hA, hlim⟩ := exists_subsequence_bounded_ordered_pairings
      (T i) (fun j => ‖T i j‖) (fun _ => norm_nonneg _) (fun j v => (T i j).le_opNorm v)
      (fun n => u i (s n)) (C i) (fun n k => hU i (s n) k)
    refine ⟨ψ, hψ, fun j k l => conj (A j k l), ?_, ?_⟩
    · intro j k l
      simpa only [RCLike.norm_conj] using hA j k l
    · intro j k l
      exact ((Complex.continuous_conj.tendsto (A j k l)).comp (hlim j k l)).congr
        (fun n => inner_conj_symm _ _)
  obtain ⟨σ, hσ, hChoices⟩ := exists_diagonal_with_countable_tails P step
  refine ⟨σ, hσ, fun i => ?_⟩
  obtain ⟨s, τ, ρ, _, hρ, ⟨L, hL, hlim⟩, hTail⟩ := hChoices i
  exact ⟨L, hL, fun j k l => tendsto_of_strictSubsequence_tail
    (fun n => inner ℂ (u i n l) (T i j (u i n k))) _ σ τ ρ s hρ hTail (hlim j k l)⟩

end Burnett.Microlocal.CountableAuxiliaryCharts
