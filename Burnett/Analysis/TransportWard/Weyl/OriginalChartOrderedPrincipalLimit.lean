import Burnett.Analysis.TransportWard.Weyl.OriginalChartWeylQuadraticWindow
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylQuadraticPrincipalLimit

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.RicciSymbol Burnett.A03
open UnitNullCompactness CotangentAngularExtension Burnett.C04 Burnett.C02
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.A02.FrequencySplit
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings
  locallyUniformlyConverges_comp_strictMono)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Topology Manifold BigOperators ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "J" => OrderedPair

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original chart limit of the actual ordered Weyl principal variation.
The Euler limit and the cubic reduction use the same windows and Weyl
action, with the same projected-measure subsequence throughout. -/
theorem exists_originalChartWeylOrderedPrincipalLimit
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
    let a := originalChartTransportSymbol q.center f
    let β := sharedInfraredTransportSymbol wardFixedTestCutoff a
    let βᵣ (x ξ : E₀) := (β x (WithLp.ofLp ξ) : ℂ)
    let b' (x : E₀) (i : J) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B q.center x) i.1 i.2
    ∃ (χ : D) (θ : SchwartzMap E₀ ℝ) (R : ℝ) (Kplus L : Set E₀)
      (hχc : tsupport (χ : E₀ → ℝ) ⊆ U)
      (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ βᵣ) R R),
      IsCompact L ∧ (∀ x ∈ L, θ x = 1) ∧ (∀ x ∉ L, ∀ ξ, a x ξ = 0) ∧
      HasCompactSupport (θ : E₀ → ℝ) ∧ ContDiff ℝ ∞ (Function.uncurry βᵣ) ∧
      (∀ x ∉ L, ∀ ξ, βᵣ x ξ = 0) ∧
      IsCompact Kplus ∧ tsupport (θ : E₀ → ℝ) ⊆ interior Kplus ∧ Kplus ⊆ q.ball.closedBall ∧
      IsCompact q.ball.closedBall ∧ Convex ℝ q.ball.closedBall ∧
      (∀ x ∈ Kplus, (χ : E₀ → ℝ) x = 1) ∧
      let Z₀ n := fixedWeylPerturbationSchwartz B g hB hg c χ hχc (σ n)
      let P := windowedWeylLeftSymbol θ βᵣ R hAmp
      let C (a d : Index) (i j k : J) (x : E₀) := Complex.ofReal
        (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b'
          (χ : E₀ → ℝ) a d i j k x)
      ∃ Z W : ℕ → RealEnergyField J,
        (∀ n i, (Z n).val i = Z₀ n i) ∧
        (∀ n i x, (W n).val i x = (-Complex.I) * firstOrderAction P (Z₀ n i) x) ∧
        (∀ n i, tsupport ((W n).val i : E₀ → ℂ) ⊆ tsupport (θ : E₀ → ℝ)) ∧
        Tendsto (fun n => ∫ x in tsupport (θ : E₀ → ℝ),
          (principalVariationDensity C (Z n).val (fun i => (W n).val i) x).re) atTop
          (𝓝 (4 * ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E₀ q.center).source},
            chartHamiltonDerivative q.center B hSig.isNondegenerate f p.val ∂μ)) := by
  intro c U a β βᵣ b'
  obtain ⟨χ, θ, R, Kplus, L, hχc, hAmp, hL, hθL, haOff, hθComp, hβᵣ, hβᵣOff,
    hKplus, hθInner, hBall, hBallCompact, hBallConvex, hχKplus, hLimit⟩ :=
    exists_originalChartWeylQuadraticWindow r B g hB hSig hg hSigG hconv hb hv σ hσ
      A hA μ hμ q ν hf hRep f hfTest hfOdd hfLocal
  have hχθ (x : E₀) (hx : x ∈ tsupport (θ : E₀ → ℝ)) :
      (χ : E₀ → ℝ) =ᶠ[𝓝 x] fun _ : E₀ => (1 : ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds (hθInner hx)] with y hy
    exact hχKplus y (interior_subset hy)
  obtain ⟨S, hS, hThreshold, hOff⟩ := hfLocal
  have hSChart : S ⊆ (chartAt E₀ q.center).source := fun x hx => (hThreshold hx).1
  obtain ⟨_, _, haOffS, haDiff, haHom, haOdd⟩ :=
    originalChartTransportSymbol_properties q.center f hfTest hfOdd hS hSChart hOff
  obtain ⟨_, _, hTail⟩ := sharedInfraredTransportSymbol_radian_properties wardFixedTestCutoff
    a (c.chart '' S) wardFixedTestCutoff_profile_one wardFixedTestCutoff_profile_zero
    haDiff haOffS haHom
  have hθβ (x ξ : E₀) (h : βᵣ x ξ ≠ 0) : θ x = 1 :=
    hθL x (by by_contra hn; exact h (hβᵣOff x hn ξ))
  have hReal (x ξ : E₀) : conj (βᵣ x ξ) = βᵣ x ξ := Complex.conj_ofReal _
  have hOdd (x ξ : E₀) : βᵣ x (-ξ) = -βᵣ x ξ := by
    let v (η : E₀) := a x (WithLp.ofLp η)
    have hv (η : E₀) : v (-η) = -v η := haOdd x (WithLp.ofLp η)
    have hNeg := wardFixedTestCutoff_odd v hv ξ
    change Complex.ofReal (fixedInfraredSymbol wardFixedTestCutoff 0 v (-ξ)) =
      -Complex.ofReal (fixedInfraredSymbol wardFixedTestCutoff 0 v ξ)
    rw [hNeg, Complex.ofReal_neg]
  obtain ⟨R', hR'⟩ := hθComp.isCompact.isBounded.subset_closedBall (0 : E₀)
  have hθOff (x : E₀) (hx : x ∉ Metric.closedBall (0 : E₀) R') : θ x = 0 := by
    by_contra hn
    exact hx (hR' (subset_tsupport (θ : E₀ → ℝ) hn))
  have hScaled := compactWindowedWeylAmplitude_scaled_orderOne θ βᵣ (θ.smooth _) hβᵣ R' hθOff hTail
  have hNormalized := scaledJointOrderOne_of_compactRadianSymbol βᵣ hβᵣ hL hβᵣOff hTail
  have hbσ : AuxiliaryAdmissibility.CompactDhBound r B (g ∘ σ) := by
    intro K hK
    obtain ⟨D, hD, hBound⟩ := hb K hK
    exact ⟨D, hD, fun n => hBound (σ n)⟩
  obtain ⟨Z, W, hZ, hW, hWS, hDiff⟩ := exists_originalWeylQuadraticPrincipalLimit
    r B (g ∘ σ) hB (fun n => hg (σ n)) hSig (fun n => (hSigG (σ n)).isSymmetric)
    (locallyUniformlyConverges_comp_strictMono r B g hconv σ hσ) hbσ q.center χ hχc θ βᵣ R
    hAmp (radianOrdinaryDirectionalAmplitudeBounds_of_scaled _ _ _ hScaled)
    hθβ θ.continuous hθComp hNormalized hReal hOdd hχθ
  refine ⟨χ, θ, R, Kplus, L, hχc, hAmp, hL, hθL, haOff, hθComp, hβᵣ, hβᵣOff,
    hKplus, hθInner, hBall, hBallCompact, hBallConvex, hχKplus, Z, W, hZ, hW, hWS, ?_⟩
  let C (a d : Index) (i j k : J) (x : E₀) := Complex.ofReal
    (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b'
      (χ : E₀ → ℝ) a d i j k x)
  have hInput (n : ℕ) (i : SymmetricMetricSlot) :
      (symmetricMetricScale i : ℂ) •
        (fixedWeylPerturbationSchwartz B (g ∘ σ) hB (fun n => hg (σ n)) c χ hχc n i.val :
          E₀ → ℂ) =
      (((symmetricMetricScale i : ℂ) • fixedWeylPerturbationSchwartz B g hB hg c χ hχc (σ n) i.val :
        SchwartzMap E₀ ℂ) : E₀ → ℂ) := by
    funext x
    rfl
  have hIntegral (n : ℕ) :
      (∫ x in tsupport (θ : E₀ → ℝ), (principalVariationDensity C (Z n).val
        (fun i => (W n).val i) x).re) =
      ∫ x, (principalVariationDensity C (Z n).val (fun i => (W n).val i) x).re := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hOut (i : J) : x ∉ tsupport ((W n).val i : E₀ → ℂ) := fun h => hx (hWS n i h)
    have hValue (i : J) : (W n).val i x = 0 := image_eq_zero_of_notMem_tsupport (hOut i)
    have hD (i : J) : fderiv ℝ ((W n).val i : E₀ → ℂ) x = 0 :=
      fderiv_of_notMem_tsupport ℝ (hOut i)
    simp only [principalVariationDensity, hValue, hD, ContinuousLinearMap.zero_apply,
      zero_mul, mul_zero, add_zero, Finset.sum_const_zero, Complex.zero_re]
  dsimp only [Function.comp_apply] at hLimit hDiff
  have hSub := hLimit.sub hDiff
  simp only [sub_zero] at hSub
  change Tendsto (fun n => ∫ x in tsupport (θ : E₀ → ℝ),
    (principalVariationDensity C (Z n).val (fun i => (W n).val i) x).re) atTop _
  refine hSub.congr fun n => ?_
  rw [hIntegral n]
  simp only [hInput, c, βᵣ, β, a, sub_sub_cancel]
  rfl

end Burnett.V03.Palatini
