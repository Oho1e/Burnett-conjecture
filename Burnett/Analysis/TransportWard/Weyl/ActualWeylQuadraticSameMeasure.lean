import Burnett.Analysis.TransportWard.Weyl.ActualWeylImaginarySameMeasure
import Burnett.Analysis.TransportWard.Weyl.NormalizedTestedVacuum
import Burnett.Analysis.TransportWard.Weyl.DirectionalBoundsFromScaled
import Burnett.Analysis.TransportWard.Weyl.ActualWeylCompactMatrixTest
import Burnett.Analysis.TransportWard.Weyl.WeylCompactMatrixPair
import Burnett.Analysis.TransportWard.Weyl.TestedVacuumLimit
import Burnett.Analysis.TransportWard.Weyl.EulerWeylLocality
import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput

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

open private linearizedCoordinateDensityEuler_eq_of_germ from Burnett.Analysis.TransportWard.Weyl.EulerWeylLocality

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

/-- The complexified Euler action on a real variation is its real Euler action. -/
private theorem complexLinearizedCoordinateDensityEuler_ofReal (S : I → Mat)
    (b h : E₀ → I → ℝ) (x : E₀) (i : I) :
    complexLinearizedCoordinateDensityEuler S b (fun y j => (h y j : ℂ)) x i =
      (linearizedCoordinateDensityEuler S b h x i : ℂ) := by
  apply Complex.ext
  · rfl
  · change linearizedCoordinateDensityEuler S b (fun _ _ => 0) x i = 0
    change deriv (fun t : ℝ => coordinateDensityEuler S (fun y => b y + t • (0 : I → ℝ)) x i) 0 = 0
    simp only [smul_zero, add_zero, deriv_const]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The exact tested vacuum relation for the original real quadratic Weyl
pair. The remaining hypothesis is the actual Taylor remainder limit on
this same cutoff input, operator, and subsequence. -/
theorem tendsto_preferredLocalizedEulerWeylQuadraticPair_sameMeasure_of_actualRemainder
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
    (Tendsto (fun n => 2 * (∫ x in U, ∑ i : I,
      conj (firstOrderAction P (w n i) x) *
        (quadraticPathRemainder (fun t => f n t x i) : ℂ)).im) atTop (𝓝 0)) →
    Tendsto (fun n => (∫ x in U, ∑ i : I,
      conj ((-Complex.I) * firstOrderAction P (w n i) x) *
        Complex.ofReal (deriv (deriv (fun t => f n t x i)) 0)).re) atTop
      (𝓝 (4 * ∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
  intro c U S b h f hχc w P H hRem
  let βC (x ξ : E₀) : ℂ := β x (WithLp.ofLp ξ)
  have hΘβ (x ξ : E₀) (hx : βC x ξ ≠ 0) : θ x = 1 := by
    apply hθL x
    by_contra hxL
    exact hx (by simp only [βC, hβS x hxL, Complex.ofReal_zero])
  have hReal (x ξ : E₀) : conj (βC x ξ) = βC x ξ := Complex.conj_ofReal _
  have hOdd (x ξ : E₀) : βC x (-ξ) = -βC x ξ := by
    have he : WithLp.ofLp (-ξ) = -(WithLp.ofLp ξ : Covector) := rfl
    simp only [βC, he, hβOdd, Complex.ofReal_neg]
  have hAmpDir := radianOrdinaryDirectionalAmplitudeBounds_of_scaled _ R R hAmp
  obtain ⟨Aop, hAct, hASupp, hASym, _⟩ := exists_windowedWeylCompactMatrixTest (ι := I)
    θ βC R hAmpCompact hAmpDir hΘβ hθ hθc hβscaled hReal hOdd
  let gσ (n : ℕ) := g (σ n)
  have hgσ (n : ℕ) : IsSmooth (gσ n) := hg (σ n)
  let T := compactMatrixTestEquiv I
  let Q := compactTransportOp Aop
  obtain ⟨source, input, linear, quadratic, rem, _, hInput, hLinear, hQuadratic, hRemainder, hVac⟩ :=
    exists_normalizedChart_tested_vacuum B gσ hB hgσ hSig (fun n => hSigG (σ n))
      (fun n => hv (σ n)) q.center χ hχc
  have hInputW (n : ℕ) (i : I) : (input n).val i = w n i := by
    have hh := (contDiffOn_normalizedChartMetric (gσ n) (hgσ n) q.center).sub
      (contDiffOn_normalizedChartMetric B hB q.center)
    have hc := normalizedChartCutoffTest_eq_weylPerturbation B gσ hB hgσ q.center χ hχc n i hh
    ext x
    change (input n).val i x = ((symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B gσ hB hgσ c χ hχc n i.val) x
    rw [← hc, chartMetricCutoffTest_apply]
    exact hInput n x i
  have hu : Tendsto (fun n => T (input n)) atTop (𝓝 0) := by
    apply tendsto_compactMatrixTestEquiv_zero
    intro i
    simp only [hInputW]
    exact (exists_original_normalizedWeylPerturbation_bounds r B g hB hg hSig.isNondegenerate
      hconv hb c χ hχc i).2.comp hσ.tendsto_atTop
  have hθχ : tsupport θ ⊆ tsupport (χ : E₀ → ℝ) := fun x hx =>
    subset_tsupport (χ : E₀ → ℝ) (by
      change (χ : E₀ → ℝ) x ≠ 0
      rw [(hχθ x hx).self_of_nhds]
      exact one_ne_zero)
  have hTU : tsupport θ ⊆ U := hθχ.trans hχc
  have hPair (n : ℕ) (G : CompactSchwartzComponents I) (V : E₀ → I → ℝ)
      (hV : ∀ x i, G.val i x = ((χ : E₀ → ℝ) x * V x i : ℝ)) :
      ⟪Q (T (input n)), T G⟫_ℂ =
        ∫ x in U, ∑ i, conj (firstOrderAction P (w n i) x) * (V x i : ℂ) := by
    have hp : ∀ x ∈ tsupport θ, ∀ i, G.val i x = (V x i : ℂ) := by
      intro x hx i
      rw [hV x i, (hχθ x hx).self_of_nhds, one_mul]
    simpa only [Q, T, compactTransportOp_apply, hAct, hInputW] using
      compactMatrixTest_inner_eq_chart_of_plateau (chartAt E₀ q.center).open_target hTU
        (Aop (input n)) G (fun x i => (V x i : ℂ)) (hASupp _) hp
  have hTest (n : ℕ) :
      ⟪Q (T (input n)), T source + T (linear n) + ((1 / 2 : ℝ) : ℂ) • T (quadratic n) + T (rem n)⟫_ℂ = 0 := by
    have hz : T source + T (linear n) + ((1 / 2 : ℝ) : ℂ) • T (quadratic n) + T (rem n) = 0 := by
      simpa only [map_add, map_smul, map_zero] using congrArg T (hVac n)
    rw [hz, inner_zero_right]
  have hLinearSameMeasure :=
    tendsto_preferredLocalizedEulerWeylImaginaryPair_sameMeasure r B g hB hSig hg
      hsG hnG
      hconv hb hv σ hσ A hA μ hμ q ν hf hRep K hK hSub χ hχ a β L hL hLU haS hβS
      haDiff hβDiff haD R₀ hMatch θ hθ hθc hθL hχθ R hAmpCompact hAmpDir hβscaled
  have hLinPair : Tendsto (fun n => 2 * (⟪Q (T (input n)), T (linear n)⟫_ℂ).im)
      atTop (𝓝 (4 * ∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
    refine hLinearSameMeasure.congr (fun n => ?_)
    rw [hPair n (linear n) _ (hLinear n)]
    congr 2
    apply setIntegral_congr_fun (chartAt E₀ q.center).open_target.measurableSet
    intro x hx
    apply Finset.sum_congr rfl
    intro i _
    have he : ∀ y ∈ U, ∀ j,
        (symmetricMetricScale j * fixedComponent B g c (σ n) j.val y : ℝ) = h n y j :=
      fun y hy j => (normalizedChartPerturbation_eq_fixedComponent B g q.center (σ n) y hy j).symm
    have hgerm : (fun y j => (symmetricMetricScale j * fixedComponent B g c (σ n) j.val y : ℝ)) =ᶠ[𝓝 x] h n := by
      filter_upwards [(chartAt E₀ q.center).open_target.mem_nhds hx] with y hy
      exact funext (he y hy)
    rw [complexLinearizedCoordinateDensityEuler_ofReal]
    have hLocal := linearizedCoordinateDensityEuler_eq_of_germ S b hgerm i
    exact congrArg (fun t : ℝ => conj (firstOrderAction P (w n i) x) * Complex.ofReal t) hLocal
  have hRemPair : Tendsto (fun n => 2 * (⟪Q (T (input n)), T (rem n)⟫_ℂ).im) atTop (𝓝 0) := by
    exact hRem.congr (fun n => by rw [hPair n (rem n) _ (hRemainder n)])
  have hQuad := tendsto_variational_quadratic_pairing_of_tested_vacuum Q hASym (T source)
    (fun n => T (input n)) hu (fun n => T (linear n)) (fun n => T (quadratic n)) (fun n => T (rem n))
    (∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K))) hTest hLinPair hRemPair
  have hResult := hQuad.neg
  rw [neg_neg] at hResult
  refine hResult.congr (fun n => ?_)
  rw [hPair n (quadratic n) _ (hQuadratic n)]
  have hi (x : E₀) :
      (∑ i : I, conj ((-Complex.I) * firstOrderAction P (w n i) x) *
        Complex.ofReal (deriv (deriv (fun t => f n t x i)) 0)) =
      Complex.I * ∑ i : I, conj (firstOrderAction P (w n i) x) *
        Complex.ofReal (deriv (deriv (fun t => f n t x i)) 0) := by
    rw [Finset.mul_sum]
    simp only [map_mul, map_neg, Complex.conj_I, neg_neg, mul_assoc]
  simp only [hi, integral_const_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  rfl

end Burnett.V03.Palatini
