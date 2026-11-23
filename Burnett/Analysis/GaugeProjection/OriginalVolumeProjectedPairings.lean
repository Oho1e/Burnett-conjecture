import Burnett.Analysis.Microlocal.OriginalVolumeCurlAmplitudes
import Burnett.Analysis.Microlocal.OriginalVolumePairingLimits
import Burnett.Analysis.GaugeProjection.IntrinsicWeightedGradient
import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedNorms
import Burnett.Analysis.GaugeProjection.ProjectedDefectMixedMetricPairings

set_option autoImplicit false
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.P01

open Filter Set MeasureTheory Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ManifoldMetricTransition (coordinateBilinear)
open Burnett.F05.OriginalCoordinateCurl Burnett.F05.ChartVolumeBridge Burnett.F05.ChartVolumeAmplitude
open Burnett.F05.ActualCoordinateCurlDensity (chartRoundAmplitude originalVolume_round_mixedPairing_witness)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Topology Matrix NNReal ComplexConjugate Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The actual projected derivatives have the pairings of the same chart trace,
with the background half-density on the support of the fixed cutoff. -/
def RepresentsVolumeProjectedPairings (B : Field (M := M)) (g : ℕ → Field (M := M))
    (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) : Prop :=
  ∃ (d : D) (z : ℕ → ProjectionSchwartzMatrix),
    EqOn (d : CoordinateSpace → ℝ) (chartHalfDensity B q.center)
      (tsupport (q.cutoff : CoordinateSpace → ℝ)) ∧
    (∀ n x i j, z n i j x = ((q.cutoff.val x *
      (metricComponents (coordinateBilinear (g (σ n)) q.center) x i j -
        metricComponents (coordinateBilinear B q.center) x i j) : ℝ) : ℂ)) ∧
    ∀ (α β : Index) (m a : BoundedSymbol CoordinateSpace),
      ContDiffOn ℝ ∞ (m : CoordinateSpace → ℂ) ({0}ᶜ : Set CoordinateSpace) →
      DegreeZero (m : CoordinateSpace → ℂ) → (∀ x, conj (a x) = a x) →
      ContDiff ℝ ∞ (a : CoordinateSpace → ℂ) → HasCompactSupport (a : CoordinateSpace → ℂ) →
      let V s n (k : OrderedPair) := symbolCLM (physicalCoefficient d)
        ((coordinateDerivative s (projectionFullSchwartz (z n) k.1 k.2)).toLp 2 volume)
      ∀ i j : OrderedPair,
        Tendsto (fun n => inner ℂ (V α n i) (symbolCLM a (fourierMultiplier m (V β n j)))) atTop
          (𝓝 (∫ x : Chart q.ball,
            let ξ : CoordinateSpace := x.2
            let P := principalGaugeProjectionMatrix ξ
            a x.1 * m ξ * ((ξ α : ℂ) * (ξ β : ℂ)) *
              (P * chartRoundAmplitude q.ball ν hfin x * Pᴴ) j i ∂traceMeasure ν))

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A chart witness from the original gradient extraction supplies the actual
pairing premise of the fixed gauge projection on the same subsequence. -/
theorem representsVolumeProjectedPairings_of_matrixDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hDh : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin) :
    RepresentsVolumeProjectedPairings B g q σ ν hfin := by
  let f := g ∘ σ
  have hf (n : ℕ) : IsSmooth (f n) := hg (σ n)
  have hconvf := locallyUniformlyConverges_comp_strictMono r B g hconv σ hσ
  have hDhf : AuxiliaryAdmissibility.CompactDhBound r B f := by
    intro S hS
    obtain ⟨C, hC, hbd⟩ := hDh S hS
    exact ⟨C, hC, fun n => hbd (σ n)⟩
  let c := q.center
  let η := q.cutoff
  let K := tsupport (η : CoordinateSpace → ℝ)
  let U := (chartAt CoordinateSpace c).target
  let coords (T : Field (M := M)) := metricComponents (coordinateBilinear T c)
  have hη : K ⊆ U := q.cutoff_support.trans q.ball_in_chart
  have hK : IsCompact K := test_compactSupport η
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  obtain ⟨d, z, hd, hz, _⟩ :=
    exists_intrinsic_originalGradient_halfDensity_error_tendsto_zero r B f hB hf hn hconvf c η hη
  refine ⟨d, z, hd, hz, ?_⟩
  obtain ⟨G, G₀, hsG', hs₀, hnear, hnear₀⟩ := exists_openChartMetricRepresentatives hK hU hη
    (fun n => coords (f n)) (coords B) (fun n => contDiffOn_metricComponents (f n) (hf n) c)
    (contDiffOn_metricComponents B hB c)
  have near n x (hx : x ∈ K) := (hnear n).filter_mono (nhds_le_nhdsSet hx)
  have near₀ x (hx : x ∈ K) := hnear₀.filter_mono (nhds_le_nhdsSet hx)
  have hct : TendstoUniformlyOn G G₀ atTop K :=
    ((components_uniform_of_physical_C0loc r f B hconvf c K hK hη).congr
      (Eventually.of_forall fun n x hx => (near n x hx).eq_of_nhds.symm)).congr_right
      (fun x hx => (near₀ x hx).eq_of_nhds.symm)
  obtain ⟨C, hC, hRaw⟩ := exists_rawComponentDerivative_bound_of_original r B f hB hf hn
    hconvf hDhf c K hK hη
  let L : ℝ≥0 := ⟨4 * C, by positivity⟩
  have hD n j k x (hx : x ∈ K) : ‖fderiv ℝ (fun y => G n y j k - G₀ y j k) x‖ ≤ (L : ℝ) := by
    have e : (fun y => G n y j k - G₀ y j k) =ᶠ[𝓝 x]
        (fun y => coords (f n) y j k - coords B y j k) := by
      filter_upwards [near n x hx, near₀ x hx] with y h₁ h₂
      rw [h₁, h₂]
    rw [e.fderiv_eq]
    exact coordinate_opNorm_le _ C hC (fun s => hRaw n (j,k) s x hx)
  let ψ := chartVolumeWeightedCutoff B hB hn c η hη
  have hψ := (chartVolumeWeightedCutoff_tsupport B hB hn c η hη).trans hη
  let gradient s n (k : OrderedPair) := originalGradientSchwartz B f hB hf c ψ hψ n (s,k)
  let W s n (k : OrderedPair) := originalGradient_volumeWeightedL2 B g hB hg hn c η hη (σ n) (s,k)
  obtain ⟨Cw, _, hBound⟩ := exists_originalVolumeJet_uniform_bound r B g hB hg hn hconv hDh q
  have rawAE s n k : (W s n k : CoordinateSpace → ℂ) =ᵐ[volume] fun y =>
      ((d.val y * η.val y * (coordinateJet (G n) y s k.1 k.2 - coordinateJet G₀ y s k.1 k.2) : ℝ) : ℂ) := by
    filter_upwards [(gradient s n k).coeFn_toLp 2 volume] with y hy
    change (gradient s n k).toLp 2 volume y = _
    rw [hy]
    change originalGradientSchwartz B f hB hf c ψ hψ n (s,k) y = _
    rw [originalGradientSchwartz_apply_rawJet]
    simp only [ψ, chartVolumeWeightedCutoff_apply]
    by_cases hyK : y ∈ K
    · have hJ := projectedChart_coordinateJet_eq_of_eventuallyEq ((near n y hyK).sub (near₀ y hyK))
      have he := congrFun (congrFun (congrFun hJ s) k.1) k.2
      have hsub : coordinateJet (fun x => G n x - G₀ x) y s k.1 k.2 =
          coordinateJet (G n) y s k.1 k.2 - coordinateJet G₀ y s k.1 k.2 := by
        simp only [coordinateJet, Pi.sub_apply, fderiv_fun_sub ((hsG' n k.1 k.2).differentiable (by simp) y)
          ((hs₀ k.1 k.2).differentiable (by simp) y), ContinuousLinearMap.sub_apply]
      change coordinateJet (fun x => G n x - G₀ x) y s k.1 k.2 =
        coordinateJet (fun x => coords (f n) x - coords B x) y s k.1 k.2 at he
      rw [← he, hsub, hd hyK]
      push_cast
      ring
    · simp [image_eq_zero_of_notMem_tsupport hyK]
  let zG n := localizedMetricSchwartz (G n) G₀ η.val (test_smooth η) (test_compactSupport η) (hsG' n) hs₀
  have hzG : zG = z := by
    funext n i j
    ext y
    rw [hz n y i j]
    change ((η.val y * (G n y i j - G₀ y i j) : ℝ) : ℂ) =
      ((η.val y * (coords (f n) y i j - coords B y i j) : ℝ) : ℂ)
    by_cases hy : y ∈ K
    · rw [(near n y hy).eq_of_nhds, (near₀ y hy).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  intro α β m a hm hm0 har ha hac V i j
  let p (x : Chart q.ball) : CoordinateSpace := x.1
  let ξ (x : Chart q.ball) : CoordinateSpace := x.2
  have hp : Measurable p := (continuous_subtype_val.comp continuous_fst).measurable
  have hξ : Measurable ξ := (continuous_subtype_val.comp continuous_snd).measurable
  obtain ⟨hInt, hPair⟩ := originalVolume_round_mixedPairing_witness r B g hB hg hn hsB hsG hconv hDh
    q σ hσ ν hfin hRep a ha.continuous α β
  have mixed := projectedLocalizedMetric_weighted_mixedPairing_tendsto (traceMeasure ν) p ξ
    (chartRoundAmplitude q.ball ν hfin) hp hξ m a hm hm0 har ha.continuous.measurable ha hac
    U hU G G₀ η.val (test_smooth η) (test_compactSupport η) hη hsG' hs₀ hct L hD
    d (physicalCoefficient d) (fun _ => rfl) W rawAE Cw (fun s n k => hBound (σ n) (s,k))
    α β hInt hPair i j
  simpa only [V, ← hzG, zG, p, ξ] using mixed

/-- The raw and projected pairings use one refinement and the same chart
trace. The projected pairing requires no input witness beyond the original metrics. -/
theorem exists_countable_originalVolume_projected_mixedPairings {I : Type*} [Countable I]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hDh : AuxiliaryAdmissibility.CompactDhBound r B g)
    (charts : I → CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∀ i,
      let q := charts i
      let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)
      ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        RepresentsCompactJetPairings q.ball w (s ∘ t) ν hfin ∧
        RepresentsVolumeProjectedPairings B g q (s ∘ t) ν hfin := by
  obtain ⟨t, ht, hCharts⟩ := exists_countable_originalVolume_matrixDensities r B g hB hg hn
    hconv hDh charts s hs
  refine ⟨t, ht, fun i => ?_⟩
  obtain ⟨ν, hfin, hRep⟩ := hCharts i
  exact ⟨ν, hfin, hRep, representsVolumeProjectedPairings_of_matrixDensity r B g hB hg hn hsB hsG
    hconv hDh (charts i) (s ∘ t) (hs.comp ht) ν hfin hRep⟩

end Burnett.P01
