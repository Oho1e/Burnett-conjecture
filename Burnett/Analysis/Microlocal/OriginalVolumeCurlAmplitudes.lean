import Burnett.Analysis.Microlocal.CoordinateCurlRows

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.F05.ActualCoordinateCurlDensity

open MeasureTheory Filter Set Matrix Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.CoordinateCurl Burnett.F05.OriginalCoordinateCurl Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.SmoothBaseTests Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.RowKernelDensity Burnett.Microlocal.AngularCommutator
open Burnett.Microlocal.FixedSubsequenceSeparableExtension Burnett.Microlocal.SeparablePositive
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped ContDiff ENNReal Topology Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The physical curl rows vanish on exactly the trace density of the
already selected volume-weighted gradient pairings in this chart. -/
theorem ae_originalVolume_curlRows_same_density
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ S : Set M, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict S) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ slot : CurlSlot, ∀ᵐ x ∂traceMeasure ν,
      (fun i => curlMatrix (roundCovector x) slot i) ᵥ*
        chartPhysicalCovariance q.ball ν hfin x = 0 := by
  let v := volumeModeInput B hB hn q
  have hχ := v.cutoff_support.trans v.ball_in_chart
  obtain ⟨θ, _, hOne⟩ := exists_chartCurl_plateau q.ball q.center q.ball_in_chart
  have hθ : ∀ x ∈ tsupport (v.cutoff : Space → ℝ), (θ : Space → ℝ) x = 1 :=
    fun x hx => hOne x (v.cutoff_support hx)
  obtain ⟨f, hs, hf, η, hη, C, _, hBound, hWeak, _, _, hSchwartz, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r B g hB hg hn hconv hb v.center v.cutoff hχ θ hθ
  have hOriginal (n : ℕ) (k : JetSlot) :
      sourceSchwartz (hs n k) η (hη n k) =
        originalGradientSchwartz B g hB hg v.center v.cutoff hχ n k :=
    congrFun (hSchwartz n) k
  have hInput (n : ℕ) (k : JetSlot) :
      (sourceSchwartz (hs n k) η (hη n k)).toLp 2 volume =
        originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart) n k :=
    congrArg (fun w : SchwartzMap Space ℂ => w.toLp 2 volume) (hOriginal n k)
  obtain ⟨_, _, _, _, _, hDensity, hLimits⟩ := hRep
  have hPSD := hDensity.mono fun _ hx => hx.1
  intro slot
  let inputs := curlRowInputs slot.1 slot.2.1 slot.2.2
  let a := curlRowCoefficients θ
  let dirs := curlRowDirections slot.1 slot.2.1
  let R := separableRowCoefficients q.ball inputs
    (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (dirs s))
  have hStrong := originalGradient_curlRow_tendsto_zero r B g hB hg hn hconv hb
    v.center v.cutoff hχ θ hθ slot.1 slot.2.1 slot.2.2
  have hRows : ∀ᵐ x ∂traceMeasure ν,
      R x ᵥ* chartPhysicalCovariance q.ball ν hfin x = 0 := by
    have h := rowPrincipal_density_kernel_of_strong_zero q.ball inputs a dirs f hs hf η hη
      C hBound hWeak σ hσ ν hfin hPSD
      (fun J _ b m hb hm hd i j => by simpa only [hInput] using hLimits J b m hb hm hd i j)
      (by simpa only [inputs, a, dirs, hOriginal] using hStrong)
    exact h.2.mono fun _ hx => hx.2
  filter_upwards [hRows] with x hx
  have hcoeff : R x = Complex.I • (fun i => curlMatrix (roundCovector x) slot i) := by
    ext i
    exact curl_separableRowCoefficients_eq q.ball θ hOne x slot i
  rw [hcoeff, Matrix.smul_vecMul] at hx
  exact (smul_eq_zero.mp hx).resolve_left Complex.I_ne_zero

/-- Contract both derivative indices against the round unit direction on
the physical orientation of the same covariance. -/
def chartRoundAmplitude (K : BallData) (ν : (JetSlot → ℂ) → Measure (Chart K))
    (hfin : ∀ v, IsFiniteMeasure (ν v)) (x : Chart K) : Matrix Pair Pair ℂ :=
  let C := gradientContraction (roundCovector x)
  C * chartPhysicalCovariance K ν hfin x * Cᴴ

/-- The same local volume-weighted jet density has a positive round amplitude
and exactly both derivative factors. The physical covariance also inherits
the symmetry of the metric components. -/
theorem ae_originalVolume_round_covariance_factor
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ S : Set M, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict S) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ x ∂traceMeasure ν,
      let N := chartPhysicalCovariance q.ball ν hfin x
      let A := chartRoundAmplitude q.ball ν hfin x
      let ξ := roundCovector x
      (∀ a b c j, N (a,b,c) j = N (a,c,b) j) ∧
      curlMatrix ξ * N = 0 ∧ A.PosSemidef ∧
      N = gradientEmbedding ξ * A * (gradientEmbedding ξ)ᴴ ∧
      ∀ i j : JetSlot, N i j = (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * A i.2 j.2 := by
  have hCurl := ae_all_iff.mpr
    (ae_originalVolume_curlRows_same_density r B g hB hg hn hconv hb q σ hσ ν hfin hRep)
  obtain ⟨_, _, _, _, _, hDensity, hLimits⟩ := hRep
  have hPSD := hDensity.mono fun _ hx => hx.1
  let v := volumeModeInput B hB hn q
  have hχ := v.cutoff_support.trans v.ball_in_chart
  let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart)
  have hSym := ae_chartPhysicalCovariance_symmetry_of_same_pairings q.ball ν hfin w σ hPSD
    hLimits (fun n a b c => originalGradient_toLp_symmetry B g hB hg hsB hsG v.center v.cutoff hχ n a b c)
  filter_upwards [hCurl, hPSD, hSym] with x hc hp hs
  dsimp only
  have hzero : curlMatrix (roundCovector x) * chartPhysicalCovariance q.ball ν hfin x = 0 := by
    ext s j
    exact congrFun (hc s) j
  obtain ⟨hA, hFactor⟩ := positive_factorCovariance_of_curl_compression (roundCovector x)
    (roundCovector x) (roundCovector_dual_pairing x) (chartPhysicalCovariance q.ball ν hfin x)
    hp.transpose (by rw [hzero, Matrix.zero_mul])
  refine ⟨hs, hzero, hA, hFactor, fun i j => ?_⟩
  have hEntry := congrFun (congrFun hFactor i) j
  exact hEntry.trans (gradient_factor_entry (roundCovector x) (chartRoundAmplitude q.ball ν hfin x) i j)

/-- Express any of the established finite separated limits by the two
derivative factors and the positive amplitude of the same density. -/
theorem originalVolume_pairing_tendsto_roundAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ S : Set M, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict S) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (J : Type) [Fintype J] (a m : J → BoundedSymbol Space)
    (ha : ∀ k, Continuous (a k : Space → ℂ))
    (hm : ∀ k, ContDiffOn ℝ ∞ (m k : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ k, DegreeZero (m k : Space → ℂ)) (i j : JetSlot) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    let b := finiteSmoothRestriction q.ball a m ha hm
    Tendsto (fun n => inner ℂ (w (σ n) i) (finiteSeparableOperator a m (w (σ n) j))) atTop
      (𝓝 (∫ x, b x * ((roundCovector x i.1 : ℂ) * (roundCovector x j.1 : ℂ) *
        chartRoundAmplitude q.ball ν hfin x j.2 i.2) ∂traceMeasure ν)) := by
  intro w b
  have hFact := ae_originalVolume_round_covariance_factor r B g hB hg hn hsB hsG
    hconv hb q σ hσ ν hfin hRep
  have hEq : (∫ x, b x * density ν hfin x i j ∂traceMeasure ν) =
      ∫ x, b x * ((roundCovector x i.1 : ℂ) * (roundCovector x j.1 : ℂ) *
        chartRoundAmplitude q.ball ν hfin x j.2 i.2) ∂traceMeasure ν := by
    apply integral_congr_ae
    filter_upwards [hFact] with x hx
    have h := hx.2.2.2.2 j i
    change density ν hfin x i j =
      (roundCovector x j.1 : ℂ) * (roundCovector x i.1 : ℂ) *
        chartRoundAmplitude q.ball ν hfin x j.2 i.2 at h
    rw [h, mul_comm (roundCovector x j.1 : ℂ) (roundCovector x i.1 : ℂ)]
  obtain ⟨_, _, _, _, _, _, hLimits⟩ := hRep
  rw [← hEq]
  exact hLimits J a m ha hm hd i j

/-- Supply the local two-slot pairing input for the projected-field theorem
with the same weighted raw sequence and the same round amplitude. -/
theorem originalVolume_round_mixedPairing_witness
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : ∀ S : Set M, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - B m)) ∞
        ((ManifoldVolume.geometricMeasure B).restrict S) ≤ ENNReal.ofReal C)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (a : BoundedSymbol Space) (ha : Continuous (a : Space → ℂ)) (α β : Axis) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    let A := chartRoundAmplitude q.ball ν hfin
    (∀ k l : Pair, Integrable (fun x => (roundCovector x α : ℂ) * (roundCovector x β : ℂ) *
      A x k l) (traceMeasure ν)) ∧
    ∀ (i j : Pair) (m : BoundedSymbol Space),
      ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space) → DegreeZero (m : Space → ℂ) →
      Tendsto (fun n => inner ℂ (w (σ n) (α,i))
        (symbolCLM a (fourierMultiplier m (w (σ n) (β,j))))) atTop
        (𝓝 (∫ x, a x.1 * m x.2 * ((roundCovector x α : ℂ) * (roundCovector x β : ℂ)) *
          A x j i ∂traceMeasure ν)) := by
  intro w A
  have hFact := ae_originalVolume_round_covariance_factor r B g hB hg hn hsB hsG
    hconv hb q σ hσ ν hfin hRep
  refine ⟨?_, ?_⟩
  · intro k l
    apply (integrable_density_entry ν hfin (β,l) (α,k)).congr
    filter_upwards [hFact] with x hx
    exact hx.2.2.2.2 (α,k) (β,l)
  · intro i j m hm hd
    have hSymbol (x : Chart q.ball) :
        finiteSmoothRestriction q.ball (fun _ : Unit => a) (fun _ : Unit => m)
          (fun _ => ha) (fun _ => hm) x = a x.1 * m x.2 := by
      rcases x with ⟨p, ξ⟩
      rw [finiteSmoothRestriction_apply]
      simp
    have h := originalVolume_pairing_tendsto_roundAmplitude r B g hB hg hn hsB hsG
      hconv hb q σ hσ ν hfin hRep Unit (fun _ => a) (fun _ => m)
      (fun _ => ha) (fun _ => hm) (fun _ => hd) (α,i) (β,j)
    simpa [w, A, finiteSeparableOperator, hSymbol, separableOperator, mul_assoc] using h

end Burnett.F05.ActualCoordinateCurlDensity
