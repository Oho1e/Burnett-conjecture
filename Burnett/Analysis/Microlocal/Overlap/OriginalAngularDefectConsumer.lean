import Burnett.Analysis.Microlocal.Overlap.CompactAngularDensityPairing
import Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudeOverlap
import Burnett.Analysis.Microlocal.OriginalVolumePairingLimits
import Burnett.Analysis.Microlocal.ChartAuxiliaryEmbedding
import Burnett.Analysis.Microlocal.ComplexMeasureBorelIntegral

/-! Read an actual local angular test from the normalized ordered amplitude entries. -/

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set Filter Function MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (cotangentCoords)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalCoordinateCurl (originalGradientSchwartz)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ComplexConjugate ContDiff Manifold Topology

local notation "E" => CoordinateSpace

/-- The symbol compensating for the cutoff on both original gradient inputs. -/
def inverseCutoffAngularSymbol (χ : D) (a : E → E → ℂ) (x ξ : E) : ℂ :=
  (((((χ : E → ℝ) x)⁻¹) ^ 2 : ℝ) : ℂ) * a x ξ

private theorem contDiffOn_inverseCutoffAngularSymbol (χ : D) {K : Set E}
    (hK : IsClosed K) (hχ : ∀ x ∈ K, (χ : E → ℝ) x ≠ 0)
    {s : Set (E × E)} {F : E × E → ℂ} (hF : ContDiffOn ℝ ∞ F s)
    (hzero : ∀ z : E × E, z.1 ∉ K → F z = 0) :
    ContDiffOn ℝ ∞ (fun z : E × E => (((((χ : E → ℝ) z.1)⁻¹) ^ 2 : ℝ) : ℂ) * F z) s := by
  apply contDiffOn_of_locally_contDiffOn
  intro z _
  let χ₁ : E × E → ℝ := fun w => (χ : E → ℝ) w.1
  have hSmooth : ContDiff ℝ ∞ χ₁ := (test_smooth χ).comp contDiff_fst
  by_cases hz : χ₁ z = 0
  · have hOut : z.1 ∉ K := fun h => hχ z.1 h hz
    refine ⟨Prod.fst ⁻¹' Kᶜ, hK.isOpen_compl.preimage continuous_fst, hOut, ?_⟩
    refine (contDiff_const (c := (0 : ℂ))).contDiffOn.congr ?_
    intro w hw
    rw [hzero w hw.2, mul_zero]
  · refine ⟨χ₁ ⁻¹' ({0}ᶜ : Set ℝ), isClosed_singleton.isOpen_compl.preimage hSmooth.continuous, hz, ?_⟩
    have hInv : ContDiffOn ℝ ∞ (fun w => (χ₁ w)⁻¹) (s ∩ χ₁ ⁻¹' {0}ᶜ) :=
      hSmooth.contDiffOn.inv (fun _ hw => hw.2)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (hInv.pow 2)).mul (hF.mono inter_subset_left)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The coordinate derivative of the original metric difference, with the actual geometric
volume half-density and the given chart cutoff, as a Schwartz representative. -/
def originalVolumeAngularInput (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (q : CompactChartInput M) (n : ℕ) (i : JetSlot) : SchwartzMap E ℂ :=
  let v := volumeModeInput B hB hnB q
  originalGradientSchwartz B g hB hg v.center v.cutoff
    (v.cutoff_support.trans v.ball_in_chart) n i

private theorem chartAngularWindow_iff {K : Set M} (r : Metric (M := M)) (q : CompactChartInput M)
    (hSub : K ⊆ q.nonzeroLocus) (z : Chart q.ball) :
    z ∈ amplitudeChartWindow r q K ↔ (z.1 : E) ∈ chartAt E q.center '' K := by
  let e := chartAt E q.center
  change e.symm z.1 ∈ K ↔ (z.1 : E) ∈ e '' K
  constructor
  · intro hz
    exact ⟨e.symm z.1, hz, e.right_inv (q.ball_in_chart z.1.property)⟩
  · rintro ⟨x, hx, hEq⟩
    rw [← hEq, e.left_inv (hSub hx).1]
    exact hx

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- An actual compactly based degree-zero Fourier action of the cutoff-compensated
symbol converges along the supplied original subsequence. Its value is the normalized
auxiliary-unit amplitude entry with both ordered derivative factors. -/
theorem tendsto_originalVolume_angularAction_normalizedAmplitudeOn [T2Space M]
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
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E → E → ℂ) (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ chartAt E q.center '' K)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (i j : JetSlot) :
    let f := originalVolumeAngularInput B g hB hg hnB q
    Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
      firstOrderAction (inverseCutoffAngularSymbol q.cutoff a) (f (σ n) j) x)
      atTop (𝓝 (∫ z in amplitudeChartWindow r q K,
        let ξ := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
        (a z.1 z.2 * (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) *
          (chartInverseCutoffComplexSquare q z * chartAuxiliaryAmplitude r q ν hfin z j.2 i.2)
          ∂traceMeasure ν)) := by
  let e := chartAt E q.center
  let C := e '' K
  let f := originalVolumeAngularInput B g hB hg hnB q
  let p := inverseCutoffAngularSymbol q.cutoff a
  have hC : IsCompact C := hK.image_of_continuousOn (e.continuousOn.mono (fun x hx => (hSub hx).1))
  have hχ : ∀ x ∈ C, (q.cutoff : E → ℝ) x ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hSub hx).2
  have hOut (x ξ : E) (hx : x ∉ C) : a x ξ = 0 := by
    by_contra h
    exact hx (hSupport ξ (subset_tsupport (fun y => a y ξ) h))
  have hP : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_inverseCutoffAngularSymbol q.cutoff hC.isClosed hχ hJoint (fun z hz => hOut z.1 z.2 hz)
  have hP0 : ContDiff ℝ ∞ (fun x => p x 0) := by
    have hPair : ContDiff ℝ ∞ (fun z : E × E => a z.1 0) := hZero.comp contDiff_fst
    have hWeighted := contDiffOn_inverseCutoffAngularSymbol q.cutoff hC.isClosed hχ
      hPair.contDiffOn (s := univ) (fun z hz => hOut z.1 0 hz)
    exact (contDiffOn_univ.mp hWeighted).comp (contDiff_id.prodMk (contDiff_const (c := (0 : E))))
  have hPSupp (ξ : E) : tsupport (fun x => p x ξ) ⊆ C :=
    tsupport_mul_subset_right.trans (hSupport ξ)
  have hDeg (x : E) : DegreeZero (p x) := by
    intro c hc ξ
    unfold p inverseCutoffAngularSymbol
    rw [hDegree x c hc ξ]
  obtain ⟨A, hA, hBound⟩ := exists_originalVolumeJet_uniform_bound r B g hB hg hnB hconv hb q
  have hProduct (n : ℕ) : ‖(f (σ n) i).toLp 2 volume‖ * ‖(f (σ n) j).toLp 2 volume‖ ≤ A * A :=
    mul_le_mul (hBound (σ n) i) (hBound (σ n) j) (norm_nonneg _) hA
  have hLim := tendsto_compactAngularAction_pairings_of_matrixDensity q.ball f σ ν hfin hRep
    p C hC hPSupp hP hP0 hDeg i j (A * A) hProduct
  have hFactor := ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv q σ hσ ν hfin hRep
  have hRight : (∫ z : Chart q.ball, p z.1 z.2 * density ν hfin z i j ∂traceMeasure ν) =
      ∫ z in amplitudeChartWindow r q K,
        let ξ := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
        (a z.1 z.2 * (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) *
          (chartInverseCutoffComplexSquare q z * chartAuxiliaryAmplitude r q ν hfin z j.2 i.2)
          ∂traceMeasure ν := by
    calc
      _ = ∫ z in amplitudeChartWindow r q K, p z.1 z.2 * density ν hfin z i j ∂traceMeasure ν := by
        rw [← integral_indicator (measurableSet_amplitudeChartWindow r q hK.isClosed.measurableSet)]
        apply integral_congr_ae
        refine Eventually.of_forall (fun z => ?_)
        by_cases hz : z ∈ amplitudeChartWindow r q K
        · rw [indicator_of_mem hz]
        · have hout : (z.1 : E) ∉ C := fun h => hz ((chartAngularWindow_iff r q hSub z).mpr h)
          rw [indicator_of_notMem hz]
          change (_ * a z.1 z.2) * _ = 0
          rw [hOut z.1 z.2 hout, mul_zero, zero_mul]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hFactor] with z hz
        have h := hz.2.1 j i
        change density ν hfin z i j = _ at h
        rw [h]
        change (_ * a z.1 z.2) * _ = _
        unfold chartInverseCutoffComplexSquare
        ring
  change Tendsto _ atTop (𝓝 _)
  rw [← hRight]
  exact hLim

end Burnett.Microlocal.Overlap
