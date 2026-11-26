import Burnett.Analysis.GaugeProjection.ReceivingProjectedDerivativePairings
import Burnett.Analysis.GaugeProjection.ReceivingProjectedPhysicalDefect
import Burnett.Analysis.GaugeProjection.FixedGaugeProjectionOrderZero
import Burnett.Analysis.Microlocal.Overlap.OriginalQuadraticTheorem

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.P01

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.Overlap
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.A02.FrequencySplit (radianFourier)
open scoped ContDiff Manifold NNReal Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The fixed real even order-zero symbol used for every actual local field. -/
def IsOriginalGeneralProjectionSymbol (a b p q : Index) : Prop :=
    ContDiff ℝ ∞ (regularizedGaugeProjectionSymbol a b p q) ∧
    (∀ ξ : E, regularizedGaugeProjectionSymbol a b p q (-ξ) = regularizedGaugeProjectionSymbol a b p q ξ) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : E,
      (max 1 ‖ξ‖) ^ n * ‖iteratedFDeriv ℝ n (regularizedGaugeProjectionSymbol a b p q) ξ‖ ≤ C

theorem originalGeneralProjection_symbol (a b p q : Index) : IsOriginalGeneralProjectionSymbol a b p q :=
  ⟨regularizedGaugeProjectionSymbol_contDiff a b p q, regularizedGaugeProjectionSymbol_even a b p q,
    regularizedGaugeProjectionSymbol_orderZero_weighted a b p q⟩

/-- The source estimate holds for all extension families at a fixed
Lipschitz bound, on the whole coordinate space. -/
def HasGeneralProjectedSourceBound
    (g : ℕ → Field (M := M)) (c : AtlasChart M) (χ : D) (u : ℕ → ProjectionSchwartzMatrix) : Prop :=
  ∀ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : ℕ → E → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
      (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j)),
      (∀ n, a n =ᶠ[𝓝ˢ (tsupport (χ : E → ℝ))]
        projectedChartInverse (metricComponents (fixedForm (g n) c))) →
      ∀ n, ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
        (fun i j x => a n x i j) (ha n) L (hL n)) (u n)‖ ≤ C

/-- One actual projected sequence for all finite exponents and all
extension families. Its angular defect uses the original global witnesses. -/
structure HasOriginalGeneralProjectionOnChart
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) : Prop where
  fixedSymbol : ∀ a b p q : Index, IsOriginalGeneralProjectionSymbol a b p q
  zeroExtended : ∀ n x i j, receivingCutoffFluctuation B g hB hg c χ hχ n i j x =
    ((((χ : E → ℝ) x * (metricComponents (fixedForm (g n) c) x i j -
      metricComponents (fixedForm B c) x i j)) : ℝ) : ℂ)
  fourierAction : ∀ n i j ξ,
    let z := receivingCutoffFluctuation B g hB hg c χ hχ n
    radianFourier (projectionFullSchwartz z i j) ξ =
      regularizedComplexGaugeProjection ξ (fun a b => radianFourier (z a b) ξ) i j
  normLimits : ProjectedFieldNormLimits (fun n => projectionFullSchwartz (receivingCutoffFluctuation B g hB hg c χ hχ n))
  sourceBound : HasGeneralProjectedSourceBound g c χ
    (fun n => projectionFullSchwartz (receivingCutoffFluctuation B g hB hg c χ hχ n))
  angularPairings : HasReceivingProjectedDerivativePairings r B c (c.chart.symm '' tsupport (χ : E → ℝ)) χ σ A
    (receivingCutoffFluctuation B g hB hg c χ hχ)
  plateauInWindow : receivingProjectionPlateau (r := r) c χ ⊆
    amplitudeCosphereWindow r (c.chart.symm '' tsupport (χ : E → ℝ))
  physicalDefect : HasReceivingProjectedPhysicalDefect r B hn c χ A μ

/-- Proposition 4.1 on the witnesses of the original quadratic theorem.
The same zero-extended metric perturbation enters the source, norms and
all angular pairings in every maximal chart. -/
theorem hasOriginalGeneralProjectionOnChart_of_originalIntrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    HasOriginalGeneralProjectionOnChart r B g hB hg hSig.isNondegenerate σ A μ c χ hχ := by
  let z := receivingCutoffFluctuation B g hB hg c χ hχ
  have hsG (n : ℕ) := (hSigG n).isSymmetric
  have hnG (n : ℕ) := (hSigG n).isNondegenerate
  obtain ⟨z₀, hz₀, hNorm, hSource⟩ := exists_maximalChartProjectedField_norms_and_uniform_source
    r g B hg hB hsG hnG hSig.isNondegenerate hv hconv hb c.chart c.compatible
    χ (test_smooth χ) (test_compactSupport χ) hχ
  have hz : z₀ = z := by
    funext n i j
    ext x
    exact hz₀ n x i j
  let K := c.chart.symm '' tsupport (χ : E → ℝ)
  have hK : IsCompact K := (test_compactSupport χ).image_of_continuousOn (c.chart.continuousOn_symm.mono hχ)
  have hKc : K ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm_mapsTo.mono_left hχ)
  have hχK : tsupport (χ : E → ℝ) ⊆ c.chart '' K := by
    intro x hx
    exact ⟨c.chart.symm x, mem_image_of_mem _ hx, c.chart.right_inv (hχ hx)⟩
  rw [hz] at hNorm hSource
  refine ⟨originalGeneralProjection_symbol, fun _ _ _ _ => rfl,
    fun n i j ξ => projectionFullSchwartz_radianFourier (z n) i j ξ, hNorm, hSource, ?_, ?_, ?_⟩
  · exact hasReceivingProjectedDerivativePairings_of_originalIntrinsicAmplitude r B g hB hg hSig.isSymmetric hsG
      hSig.isNondegenerate hnG hconv hb hv σ hσ A hA c K hK hKc χ hχK
  · intro p hp
    have hpc : projection p ∈ c.chart.source := hp.1
    have hx : (χ : E → ℝ) (fixedChartPhase c p.val).1 = 1 := hp.2
    rw [FixedCotangentChart.fixedChartPhase_of_mem c p.val hpc] at hx
    change (χ : E → ℝ) (c.chart (projection p)) = 1 at hx
    have hs : c.chart (projection p) ∈ tsupport (χ : E → ℝ) :=
      subset_tsupport _ (show (χ : E → ℝ) (c.chart (projection p)) ≠ 0 from hx.symm ▸ one_ne_zero)
    exact ⟨c.chart (projection p), hs, c.chart.left_inv hpc⟩
  · exact hasReceivingProjectedPhysicalDefect_of_originalIntrinsicAmplitude r B g hB hg hSig σ A μ hA hμ c χ

/-- Under the paper's admissibility, the same original subsequence and
physical measure work for all maximal charts and all compact cutoffs. -/
theorem exists_originalGeneralProjection
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hTime : ∃ V : ChartVectorField.Field (M := M), ChartVectorField.IsSmooth V ∧ ∀ x, B x (V x) (V x) < 0)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
      HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A ∧
      HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
      HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
      ∀ (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target),
        HasOriginalGeneralProjectionOnChart r B g hB hg hSig.isNondegenerate σ A μ c χ hχ := by
  obtain ⟨σ, hσ, A, μ, hA, _, _, _, _, _, hμ, _, _, _, _, hMoments, _, _⟩ :=
    Burnett.F07.exists_quadraticOriginalMeasure r B g hB hg hSig hSigG hTime hv hconv hb
  exact ⟨σ, hσ, A, μ, hA, hμ, hMoments,
    hasOriginalGeneralProjectionOnChart_of_originalIntrinsicAmplitude r B g hB hg hSig hSigG hv hconv hb
      σ hσ A μ hA hμ⟩

end Burnett.P01
