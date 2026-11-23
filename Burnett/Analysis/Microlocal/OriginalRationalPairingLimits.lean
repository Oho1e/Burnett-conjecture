import Burnett.Analysis.Microlocal.OriginalVolumePairingLimits
import Burnett.Analysis.Microlocal.RationalAngularSymbols

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.SmoothAngularTests
open scoped ContDiff ENNReal Topology Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- One strict subsequence of the original metric sequence gives all rational angular
Fourier modes and every prescribed countable family of spatial multipliers and compact
charts. The constants for each chart precede the choice of spatial multipliers. -/
theorem exists_countable_originalVolume_rational_pairing_limits
    {I J : Type*} [Countable I] [Countable J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C)
    (charts : I → CompactChartInput M) :
    ∃ C : I → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ a : I → J → BoundedSymbol Space,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i,
        let q := charts i
        let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)
        ∃ L : J → (RationalPolynomial × RationalPolynomial) → JetSlot → JetSlot → ℂ,
          (∀ j p k l, ‖L j p k l‖ ≤
            ((a i j).bound * (complexRationalAngularSymbol p).bound) * C i ^ 2) ∧
          ∀ j p k l, Tendsto (fun n => inner ℂ (w (σ n) l)
            (symbolCLM (a i j) (fourierMultiplier (complexRationalAngularSymbol p) (w (σ n) k))))
            atTop (𝓝 (L j p k l)) := by
  obtain ⟨e, he⟩ := exists_rationalAngular_enumeration
  letI : Countable (RationalPolynomial × RationalPolynomial) := he.countable
  obtain ⟨C, hC, hAll⟩ := exists_countable_originalVolume_pairing_limits
    (J := J × (RationalPolynomial × RationalPolynomial)) r B g hB hg hn hconv hb charts
  refine ⟨C, hC, fun a => ?_⟩
  let T (i : I) (jp : J × (RationalPolynomial × RationalPolynomial)) :=
    separableOperator (a i jp.1) (complexRationalAngularSymbol jp.2)
  obtain ⟨σ, hσ, hCharts⟩ := hAll T
  refine ⟨σ, hσ, fun i => ?_⟩
  obtain ⟨L, hL, hlim⟩ := hCharts i
  refine ⟨fun j p k l => L (j, p) k l, ?_, fun j p k l => hlim (j, p) k l⟩
  intro j p k l
  have hop : ‖T i (j, p)‖ ≤ (a i j).bound * (complexRationalAngularSymbol p).bound :=
    (T i (j, p)).opNorm_le_bound
      (mul_nonneg (a i j).bound_nonneg (complexRationalAngularSymbol p).bound_nonneg)
      (separableOperator_norm_le (a i j) (complexRationalAngularSymbol p))
  exact (hL (j, p) k l).trans (mul_le_mul_of_nonneg_right hop (sq_nonneg _))

end Burnett.Microlocal.CountableAuxiliaryCharts
