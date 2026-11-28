import Burnett.Analysis.TransportWard.Weyl.ActualWeylQuadraticSameMeasure
import Burnett.Analysis.TransportWard.Weyl.OriginalWindowedEulerRemainder

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.RicciSymbol Burnett.V02 Burnett.A03
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction scalarSchwartzProduct)
open Burnett.A02.FrequencySplit (tau)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedComponent)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open Burnett.Analysis.CarlesonEmbedding
open scoped ContDiff Topology Manifold BigOperators ComplexConjugate InnerProductSpace

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- On the original subsequence, the real quadratic Euler test has the
same factor-four physical measure limit as the genuine Weyl commutator. -/
theorem tendsto_preferredLocalizedEulerWeylQuadraticPair_sameMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (AtlasChart.atPoint q.center).chart '' K)
    (a β : E₀ → Covector → ℝ) (L : Set E₀) (hL : IsCompact L)
    (hLU : L ⊆ (chartAt E₀ q.center).target)
    (haS : ∀ x ∉ L, ∀ ξ, a x ξ = 0) (hβS : ∀ x ∉ L, ∀ ξ, β x ξ = 0)
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (hβDiff : ContDiff ℝ ∞ (uncurry β))
    (hβOdd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (haD : ∀ x (s : ℝ), 0 < s → ∀ ξ : Covector, ξ ≠ 0 → a x (s • ξ) = s * a x ξ)
    (R₀ : ℝ) (hMatch : ∀ y ξ, R₀ ≤ ‖(WithLp.toLp 2 ξ : E₀)‖ → β y ξ = a y ξ)
    (θ : E₀ → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθL : ∀ x ∈ L, θ x = 1)
    (hχθ : ∀ x ∈ tsupport θ, (χ : E₀ → ℝ) =ᶠ[𝓝 x] fun _ : E₀ => (1 : ℝ))
    (R : ℝ)
    (hAmpCompact : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ))) R R)
    (hAmp : CompactRadianScaledOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ))) R R)
    (hβscaled : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ)))) :
    let c := AtlasChart.atPoint q.center
    let U := (chartAt E₀ q.center).target
    let S := orthonormalMetricDirection
    let b := normalizedChartMetric B q.center
    let h (n : ℕ) := normalizedChartPerturbation B (g (σ n)) q.center
    let f (n : ℕ) (t : ℝ) (x : E₀) (i : I) :=
      coordinateDensityEuler S (fun y => b y + t • h n y) x i
    let hχc : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target :=
      hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left (fun _ hy => (hSub hy).1)))
    let w (n : ℕ) (i : I) := (symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B g hB hg c χ hχc (σ n) i.val
    let P := windowedWeylLeftSymbol θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ)) R hAmpCompact
    let H (p : Cosphere r) := canonicalBracket (coordinateHamiltonian (chartLowerMetric B q.center)) a
      (c.chart (projection p)) (atlasChartUnitCovector c p)
    Tendsto (fun n => (∫ x in U, ∑ i : I,
      conj ((-Complex.I) * firstOrderAction P (w n i) x) *
        Complex.ofReal (deriv (deriv (fun t => f n t x i)) 0)).re) atTop
      (𝓝 (4 * ∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
  intro c U S b h f hχc w P H
  let βC (x ξ : E₀) : ℂ := β x (WithLp.ofLp ξ)
  have hΘβ (x ξ : E₀) (hx : βC x ξ ≠ 0) : θ x = 1 := by
    apply hθL x
    by_contra hxL
    exact hx (by simp only [βC, hβS x hxL, Complex.ofReal_zero])
  have hReal (x ξ : E₀) : conj (βC x ξ) = βC x ξ := Complex.conj_ofReal _
  have hAmpDir := radianOrdinaryDirectionalAmplitudeBounds_of_scaled _ R R hAmp
  have hRem := tendsto_originalNormalizedWindowedWeylEulerRemainder r B g hB hg hSig
    (fun n => (hSigG n).isSymmetric) hconv hb q.center χ hχc θ βC R
    hAmpCompact hAmpDir hΘβ hθ hθc hβscaled hReal hχθ
  exact tendsto_preferredLocalizedEulerWeylQuadraticPair_sameMeasure_of_actualRemainder
    r B g hB hSig hg hSigG hsG hnG hconv hb hv σ hσ A hA μ hμ q ν hf hRep K hK hSub χ hχ a β L hL hLU
    haS hβS haDiff hβDiff hβOdd haD R₀ hMatch θ hθ hθc hθL hχθ R hAmpCompact hAmp hβscaled
    (hRem.comp hσ.tendsto_atTop)

end Burnett.V03.Palatini
