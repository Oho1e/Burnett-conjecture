import Burnett.Analysis.TransportWard.Weyl.OriginalWeylQuadraticSameMeasure
import Burnett.Analysis.TransportWard.Weyl.OriginalF07NestedWeylWindows
import Burnett.Analysis.TransportWard.Weyl.OriginalChartTransportSymbol
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylTransportIntegral
import Burnett.Analysis.TransportWard.Weyl.CompactWindowedWeylJets
import Burnett.Analysis.TransportWard.Weyl.SharedInfraredTransportSymbol
import Burnett.Analysis.TransportWard.Weyl.OriginalF07PatchWindow
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFixedTestWindow

set_option autoImplicit false
set_option maxHeartbeats 7700000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.RicciSymbol Burnett.V02 Burnett.A03
open UnitNullCompactness CotangentAngularExtension Burnett.C04
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.A02.FrequencySplit (fixedInfraredSymbol)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Topology Manifold BigOperators ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The genuine quadratic Euler pairing tends to the Hamilton integral
on the entire original chart. The exact compact Weyl window is covered by
patches in the same represented ball on which the input cutoff is one. -/
theorem exists_originalChartWeylQuadraticWindow
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (f : CotangentBundle M → ℝ) (hfTest : IsDegreeOneTransportTest f) (hfOdd : IsAntipodallyOdd f)
    (hfLocal : HasCompactTransportBaseSupportIn f (q.cutoffLocusAbove (1 / 2))) :
    let c := AtlasChart.atPoint q.center
    let U := (chartAt E₀ q.center).target
    let C := orthonormalMetricDirection
    let b := normalizedChartMetric B q.center
    let h (n : ℕ) := normalizedChartPerturbation B (g (σ n)) q.center
    let a := originalChartTransportSymbol q.center f
    let β := sharedInfraredTransportSymbol Burnett.C02.wardFixedTestCutoff a
    let βᵣ (x ξ : E₀) := (β x (WithLp.ofLp ξ) : ℂ)
    ∃ (χ : D) (θ : SchwartzMap E₀ ℝ) (R : ℝ) (Kplus L : Set E₀)
      (hχc : tsupport (χ : E₀ → ℝ) ⊆ U)
      (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ βᵣ) R R),
      IsCompact L ∧ (∀ x ∈ L, θ x = 1) ∧ (∀ x ∉ L, ∀ ξ, a x ξ = 0) ∧
      HasCompactSupport (θ : E₀ → ℝ) ∧ ContDiff ℝ ∞ (Function.uncurry βᵣ) ∧
      (∀ x ∉ L, ∀ ξ, βᵣ x ξ = 0) ∧
      IsCompact Kplus ∧ tsupport (θ : E₀ → ℝ) ⊆ interior Kplus ∧ Kplus ⊆ q.ball.closedBall ∧
      IsCompact q.ball.closedBall ∧ Convex ℝ q.ball.closedBall ∧
      (∀ x ∈ Kplus, (χ : E₀ → ℝ) x = 1) ∧
      let w (n : ℕ) (i : I) := (symmetricMetricScale i : ℂ) •
        fixedWeylPerturbationSchwartz B g hB hg c χ hχc (σ n) i.val
      let u (n : ℕ) (t : ℝ) (x : E₀) (i : I) :=
        coordinateDensityEuler C (fun y => b y + t • h n y) x i
      let P := windowedWeylLeftSymbol θ βᵣ R hAmp
      Tendsto (fun n => (∫ x in U, ∑ i : I,
        conj ((-Complex.I) * firstOrderAction P (w n i) x) *
        Complex.ofReal (deriv (deriv (fun t => u n t x i)) 0)).re) atTop
        (𝓝 (4 * ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E₀ q.center).source},
          chartHamiltonDerivative q.center B hSig.isNondegenerate f p.val ∂μ)) := by
  intro c U C b h a β βᵣ
  obtain ⟨S, hS, hThreshold, hZero⟩ := hfLocal
  obtain ⟨K, L, χ, θ, hK, hSK, _, hKNonzero, hLS, _, _, hχK, hθCont, hθComp, hθL, hχθ, _⟩ :=
    exists_originalF07NestedWeylWindows q f S hS hThreshold hZero
  obtain ⟨Kplus, hKplus, hθInner, hBall, hBallCompact, hBallConvex, _, hχPlateau⟩ :=
    exists_originalF07WeylPatchWindow q K hKNonzero χ hχK θ hθComp hχθ
  have hKChart : K ⊆ (chartAt E₀ q.center).source := fun x hx => (hKNonzero hx).1
  have hSChart := hSK.trans hKChart
  have hχc : tsupport (χ : E₀ → ℝ) ⊆ U :=
    hχK.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKChart))
  subst L
  obtain ⟨hL, hLU, haOff, haDiff, haHom, haOdd⟩ :=
    originalChartTransportSymbol_properties q.center f hfTest hfOdd hS hSChart hZero
  obtain ⟨hβ, hβOff, hβMatch⟩ := sharedInfraredTransportSymbol_properties
    Burnett.C02.wardFixedTestCutoff a (c.chart '' S) Burnett.C02.wardFixedTestCutoff_profile_one
    Burnett.C02.wardFixedTestCutoff_profile_zero haDiff haOff
  obtain ⟨hβᵣ, hβᵣOff, hβᵣTail⟩ := sharedInfraredTransportSymbol_radian_properties
    Burnett.C02.wardFixedTestCutoff a (c.chart '' S) Burnett.C02.wardFixedTestCutoff_profile_one
    Burnett.C02.wardFixedTestCutoff_profile_zero haDiff haOff haHom
  have hβOdd (x : E₀) (ξ : Covector) : β x (-ξ) = -β x ξ := by
    let T : E₀ ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)
    let v (η : E₀) := a x (T η)
    have hv (η : E₀) : v (-η) = -v η := by
      change a x (T (-η)) = -a x (T η)
      rw [map_neg]
      exact haOdd x (T η)
    exact Burnett.C02.wardFixedTestCutoff_odd v hv (WithLp.toLp 2 ξ)
  obtain ⟨R, hR⟩ := hθComp.isCompact.isBounded.subset_closedBall (0 : E₀)
  have hθOff : ∀ x ∉ Metric.closedBall (0 : E₀) R, θ x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hR (subset_tsupport (θ : E₀ → ℝ) hn))
  have hScaled := compactWindowedWeylAmplitude_scaled_orderOne θ βᵣ (θ.smooth _) hβᵣ R hθOff hβᵣTail
  have hNormalized := scaledJointOrderOne_of_compactRadianSymbol βᵣ hβᵣ hL hβᵣOff hβᵣTail
  have hMatch (x : E₀) (ξ : Covector) (hx : 2 ≤ ‖(WithLp.toLp 2 ξ : E₀)‖) : β x ξ = a x ξ :=
    hβMatch x ξ (lt_of_lt_of_le (by norm_num) hx)
  have hLimit := tendsto_preferredLocalizedEulerWeylQuadraticPair_sameMeasure
    r B g hB hSig hg hSigG (fun n => (hSigG n).isSymmetric) (fun n => (hSigG n).isNondegenerate)
    hconv hb hv σ hσ A hA μ hμ q ν hf hRep K hK hKNonzero χ hχK
    a β _ hL hLU haOff hβOff haDiff hβ hβOdd haHom 2 hMatch θ hθCont hθComp hθL hχθ R
    hScaled.toCompactRadianTwoPointOrderOne hScaled hNormalized
  have hTransfer := originalWeylTransportIntegral_eq_chart r B hSig.isNondegenerate hSig.isSymmetric
    q.center μ f a K hK hKChart (fun p hp hz => hZero p hp (fun hS => hz (hSK hS)))
    (fun x hx ξ hξ => originalChartTransportSymbol_eq q.center f x hx ξ hξ)
  refine ⟨χ, θ, R, Kplus, c.chart '' S, hχc, hScaled.toCompactRadianTwoPointOrderOne,
    hL, hθL, haOff, hθComp, hβᵣ, hβᵣOff, hKplus, hθInner, hBall, hBallCompact, hBallConvex, hχPlateau, ?_⟩
  dsimp only at hLimit
  rw [← hTransfer]
  exact hLimit

end Burnett.V03.Palatini
