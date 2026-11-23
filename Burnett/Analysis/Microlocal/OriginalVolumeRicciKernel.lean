import Burnett.Analysis.Microlocal.OriginalRicciPrincipalRows
import Burnett.Analysis.Microlocal.ChartRicciRoundSymbol
import Burnett.Analysis.GaugeProjection.OriginalVolumeProjectedPairings

set_option autoImplicit false
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.F05.ActualCoordinateRicciDensity

open MeasureTheory Filter Set Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.InverseField
open Burnett.F05.OriginalCoordinateCurl Burnett.F05.ActualCoordinateCurlDensity
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.RicciRow Burnett.Microlocal.RicciRemainder
open Burnett.Microlocal.FixedChartGeometricDensity Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.SmoothBaseTests Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.RowKernelDensity
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped ContDiff ENNReal Topology Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem backgroundInverse_symmetric
    (B : Field (M := M)) (hsB : IsSymmetric B) (hnB : IsNondegenerate B)
    (q : CompactChartInput M) (x : q.ball.Point) :
    IsSymmetricTensor (backgroundInverse B q.center x) := by
  let g := coordinateBilinear B q.center x
  have hs : g.IsSymm := coordinateBilinear_symmetric B hsB q.center x
  have hn : g.Nondegenerate :=
    coordinateBilinear_nondegenerate B hnB q.center (q.ball_in_chart x.property)
  change IsSymmetricTensor (matrixInverse (Burnett.Geometry.FiberMetric.covariant g coordinateBasis))
  rw [matrixInverse_covariant g hn hs coordinateBasis]
  exact Burnett.Geometry.FiberMetric.contravariant_symmetric g hn hs coordinateBasis

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The actual vacuum Ricci rows vanish on the same trace density used by
the volume-weighted raw and projected derivative pairings. -/
theorem ae_originalVolume_ricciRows_same_density
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ slot : Pair, ∀ᵐ x ∂traceMeasure ν,
      (fun i => ricciJetMatrix (backgroundInverse B q.center x.1) (roundCovector x) slot i) ᵥ*
        chartPhysicalCovariance q.ball ν hfin x = 0 := by
  let v := volumeModeInput B hB hnB q
  have hχ := v.cutoff_support.trans v.ball_in_chart
  obtain ⟨θ, hθtarget, hOne⟩ := exists_chartCurl_plateau q.ball q.center q.ball_in_chart
  have hθ : ∀ x ∈ tsupport (v.cutoff : Space → ℝ), (θ : Space → ℝ) x = 1 :=
    fun x hx => hOne x (v.cutoff_support hx)
  obtain ⟨f, hs, hf, η, hη, C, _, hBound, hWeak, _, _, hSchwartz, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r B g hB hg hnB hconv hb v.center v.cutoff hχ θ hθ
  have hOriginal (n : ℕ) (k : JetSlot) :
      sourceSchwartz (hs n k) η (hη n k) =
        originalGradientSchwartz B g hB hg v.center v.cutoff hχ n k :=
    congrFun (hSchwartz n) k
  have hInput (n : ℕ) (k : JetSlot) :
      (sourceSchwartz (hs n k) η (hη n k)).toLp 2 volume =
        originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart) n k :=
    congrArg (fun w : SchwartzMap Space ℂ => w.toLp 2 volume) (hOriginal n k)
  obtain ⟨_, _, _, _, _, hDensity, hLimits⟩ := hRep
  have hPSD := hDensity.mono fun _ hx => hx.1
  intro slot
  let inputs := termInput slot.1 slot.2
  let a := chartRicciCoefficient B hB hnB q.center θ hθtarget
  let dirs := ricciRowDirectionVector slot.2
  let R := separableRowCoefficients q.ball inputs
    (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (dirs s))
  have hStrong := chartRicciPrincipal_tendsto_zero_of_intrinsicVacuum r B g hB hg hsB hsG
    hnB hnG hconv hb q.center hv v.cutoff θ hχ hθtarget hθ slot.1 slot.2
  have hRows : ∀ᵐ x ∂traceMeasure ν,
      R x ᵥ* chartPhysicalCovariance q.ball ν hfin x = 0 := by
    have h := rowPrincipal_density_kernel_of_strong_zero q.ball inputs a dirs f hs hf η hη
      C hBound hWeak σ hσ ν hfin hPSD
      (fun J _ b m hb hm hd i j => by simpa only [hInput] using hLimits J b m hb hm hd i j)
      (by simpa only [chartRicciPrincipal, a, dirs, inputs, hOriginal] using hStrong)
    exact h.2.mono fun _ hx => hx.2
  filter_upwards [hRows] with x hx
  have hcoeff : R x = (-Complex.I) •
      (fun j => ricciJetMatrix (backgroundInverse B q.center x.1) (roundCovector x) slot j) :=
    roundBesselCoefficient_eq_ricciJetMatrix_of_cutoff_eq_one q.ball slot.1 slot.2 a
      (backgroundInverse B q.center x.1) θ x (fun _ => rfl) (hOne x.1 x.1.property)
  rw [hcoeff, Matrix.smul_vecMul] at hx
  exact (smul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

/-- The same positive round amplitude has symmetric range in the actual
complex Ricci kernel. The range conclusion holds for every input on one
trace-conull set. -/
theorem ae_originalVolume_roundAmplitude_in_ricciKernel
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    ∀ᵐ x ∂traceMeasure ν,
      let A := chartRoundAmplitude q.ball ν hfin x
      A.PosSemidef ∧ ∀ u : Pair → ℂ,
        let k (a b : Index) := (A *ᵥ u) (a, b)
        IsSymmetricComplexTensor k ∧ ∀ a b,
          complexRicciSymbol (backgroundInverse B q.center x.1) (roundCovector x) k a b = 0 := by
  have hF := ae_originalVolume_round_covariance_factor r B g hB hg hnB hsB hsG
    hconv hb q σ hσ ν hfin hRep
  have hRic := ae_all_iff.mpr (ae_originalVolume_ricciRows_same_density r B g hB hg hsB hsG
    hnB hnG hconv hb hv q σ hσ ν hfin hRep)
  obtain ⟨_, _, _, _, _, hDensity, _⟩ := hRep
  filter_upwards [hF, hRic, hDensity] with x hf hr hp
  dsimp only
  let ξ := roundCovector x
  let G := backgroundInverse B q.center x.1
  let N := chartPhysicalCovariance q.ball ν hfin x
  have hrow : ricciJetMatrix G ξ * N = 0 := by
    ext i j
    exact congrFun (hr i) j
  refine ⟨hf.2.2.1, fun u => ?_⟩
  exact factoredAmplitude_in_complexRicciKernel G ξ ξ (roundCovector_dual_pairing x)
    (backgroundInverse_symmetric B hsB hnB q x.1) N hp.1.transpose hf.1
    (by rw [hf.2.1, Matrix.zero_mul]) (by rw [hrow, Matrix.zero_mul]) u

/-- One common refinement and one trace per chart give the raw and projected
pairings and the vacuum Ricci-kernel constraint on their shared amplitude. -/
theorem exists_countable_originalVolume_RicciKernel_projected_pairings {I : Type*} [Countable I]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (charts : I → CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∀ i,
      let q := charts i
      let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)
      ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        RepresentsCompactJetPairings q.ball w (s ∘ t) ν hfin ∧
        Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) ν hfin ∧
        ∀ᵐ x ∂traceMeasure ν,
          let A := chartRoundAmplitude q.ball ν hfin x
          A.PosSemidef ∧ ∀ u : Pair → ℂ,
            let k (a b : Index) := (A *ᵥ u) (a, b)
            IsSymmetricComplexTensor k ∧ ∀ a b,
              complexRicciSymbol (backgroundInverse B q.center x.1) (roundCovector x) k a b = 0 := by
  obtain ⟨t, ht, hCharts⟩ :=
    Burnett.P01.exists_countable_originalVolume_projected_mixedPairings r B g hB hg hnB hsB hsG
      hconv hb charts s hs
  refine ⟨t, ht, fun i => ?_⟩
  obtain ⟨ν, hfin, hRep, hProj⟩ := hCharts i
  exact ⟨ν, hfin, hRep, hProj,
    ae_originalVolume_roundAmplitude_in_ricciKernel r B g hB hg hsB hsG hnB hnG hconv hb hv
      (charts i) (s ∘ t) (hs.comp ht) ν hfin hRep⟩

end Burnett.F05.ActualCoordinateRicciDensity
