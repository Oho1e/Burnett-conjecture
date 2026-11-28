import Burnett.Analysis.TransportWard.Weyl.OriginalFrozenC03TailInterface
import Burnett.Analysis.TransportWard.Weyl.OriginalC03ChartWeylLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalChartC03FreezeTail
import Burnett.Analysis.TransportClosure.OriginalRetestedFrozenTail

set_option autoImplicit false
set_option maxHeartbeats 11000000
set_option maxRecDepth 6000

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol Burnett.Fourier
open ConnectionDifference InverseField ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C01 Burnett.C02 Burnett.C03 Burnett.C04
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original chartwise transport bound follows from the frozen tail on
the very same C03 patches. The two-scale constants keep their order. -/
theorem originalChartWeyl_twoScale_of_frozenC03_tail
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (f : CotangentBundle M → ℝ) (hfTest : IsDegreeOneTransportTest f) (hfOdd : IsAntipodallyOdd f)
    (hfLocal : HasCompactTransportBaseSupportIn f (q.cutoffLocusAbove (1 / 2)))
    (hFrozen : HasOriginalFrozenC03Tail B g hB hg σ q.center f) :
    let I := ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E q.center).source},
      chartHamiltonDerivative q.center B hSig.isNondegenerate f p.val ∂μ
    ∃ C α β δ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D F ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + F * ℓ := by
  intro I
  obtain ⟨χ, θ, R, Kplus, L, hχ, hAmp, hL, hθL, haOff, hθc, _, hK, _, hKV, hV, hConvex, hχK,
    e, ℓ₀, Msrc, Ccoeff, Ccut, Cp, he, heT, heBound, hℓ₀, hMsrc, hCcoeff, hCcut, hCp, hPatch⟩ :=
    exists_originalChartWeylC03_retested_cubic_limit r B g hB hSig hg hSigG hconv hb hv
      σ hσ A hA hPair μ hμ q ν hf hRep f hfTest hfOdd hfLocal
  obtain ⟨S, hS, hsChart, hsOff⟩ := hfLocal
  have hsU : S ⊆ (chartAt E q.center).source := fun x hx => (hsChart hx).1
  have hKU : Kplus ⊆ (chartAt E q.center).target := hKV.trans q.ball_in_chart
  obtain ⟨F, hF, hFreeze⟩ := exists_originalChartWeyl_receiving_freezing_tail r B g hB hg hSig
    hconv hb σ hσ q.center f hfTest hfOdd hS hsU hsOff χ hχ Kplus L hK hKU hχK hL haOff θ hθc hθL
    e he heT heBound Ccut hCcut R hAmp
  obtain ⟨Cnear, α, β, δ₀, hα, hβ, hδ₀, hRate⟩ :=
    hFrozen Kplus q.ball.closedBall hK hV hKV hConvex q.ball_in_chart
      e he heT heBound Msrc Ccoeff Ccut Cp hMsrc hCcoeff hCcut hCp
  let W := (17 ^ 4 : ℝ) * (volume Kplus).toReal
  apply two_scale_bound_of_retested_frozen_families (J := LatticeIndex) I W Cnear F α β δ₀ hF hα hβ hδ₀
  intro δ hδ hδ'
  obtain ⟨Rδ, Gδ, ℓδ, hℓδ, hTail⟩ := hRate δ hδ hδ'
  refine ⟨Rδ, Gδ, min 1 (min ℓ₀ ℓδ), lt_min zero_lt_one (lt_min hℓ₀ hℓδ), ?_⟩
  intro ℓ hℓ hsmall
  have hℓ₁ : ℓ ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hℓBase : ℓ < ℓ₀ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hℓRate : ℓ < ℓδ := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s, d, ψ, hd, _, hVol, hCuts, hSource, hPrincipal⟩ := hPatch ℓ hℓ hℓBase
  let c := AtlasChart.atPoint q.center
  let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
  let mass (j : LatticeIndex) := ((volume : Measure E) (P j)).toReal
  let a (x ξ : E) := originalChartTransportSymbol q.center f x (WithLp.ofLp ξ)
  let βᵣ (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
  let T (w : SchwartzMap E ℂ) (x : E) :=
    (-Complex.I) * firstOrderAction
      (windowedWeylLeftSymbol θ (fun y ξ => (βᵣ y ξ : ℂ)) R hAmp) w x
  let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
    (normalizedChartMetric B q.center x) i.1 i.2
  let C (p q : Index) (i j k : OrderedPair) (x : E) := Complex.ofReal
    (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x)
  let z (n : ℕ) (j : LatticeIndex) := receivingCubicPatchField B g hB hg c (d j) (hd j) (σ n)
  let principal (n : ℕ) (j : LatticeIndex) :=
    ∫ x, (principalVariationDensity C (z n j).val (fun i => T ((z n j).val i)) x).re
  let frozen (n : ℕ) (j : LatticeIndex) :=
    let x := patchCenter ℓ j
    let G₀ := metricComponents (fixedForm B c) x
    completeCubicEnergy (frozenActionCubicLinear G₀) (frozenActionCubicQuadratic G₀) (βᵣ x) (z n j)
  have hMass : (∑ j ∈ s, mass j) ≤ W := by
    have hKfinite : (volume : Measure E) Kplus < ⊤ := hK.measure_lt_top
    have hRfinite : (((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus) ≠ ⊤ :=
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hKfinite).ne
    have h := ENNReal.toReal_mono hRfinite hVol
    have hFinite (j : LatticeIndex) : (volume : Measure E) (P j) ≠ ⊤ :=
      (isCompact_closedBall _ _).measure_lt_top.ne
    rw [ENNReal.toReal_sum (fun j _ => hFinite j), ENNReal.toReal_mul] at h
    simpa only [W, mass, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat] using h
  refine ⟨s, principal, frozen, mass, hMass, hPrincipal, ?_, ?_⟩
  · exact hTail ℓ hℓ hℓRate s d ψ hd hCuts hSource hVol
  · intro j hj
    obtain ⟨_, _, hInner, _, hIn, _, hJets⟩ := hCuts j hj
    exact hFreeze ℓ hℓ hℓ₁ (patchCenter ℓ j) (d j) (hd j) hInner
      (hIn.trans interior_subset) (fun k x => (hJets k x).1)

end Burnett.V03.Palatini
