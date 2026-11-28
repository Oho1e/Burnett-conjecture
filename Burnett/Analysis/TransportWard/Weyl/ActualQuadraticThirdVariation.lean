import Burnett.Analysis.TransportWard.Weyl.QuadraticEulerCutoffPair
import Burnett.Analysis.TransportWard.Weyl.NormalizedTestedVacuum
import Burnett.Analysis.TransportWard.Weyl.ActualWeylCompactMatrixTest

set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition MaximalChart
open Burnett.A03
open Burnett.A02.FrequencySplit (RealEnergyField)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix.Norms.Elementwise Topology

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

/-- The actual real odd Weyl output and the actual normalized input give
the exact third action variation on the original chart. -/
theorem exists_originalWeylQuadraticThirdVariation
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (c : M) (χ : D)
    (hχ : tsupport (χ : E₀ → ℝ) ⊆ (chartAt E₀ c).target)
    (θ : E₀ → ℝ) (β : E₀ → E₀ → ℂ) (R : ℝ)
    (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hDir : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hθβ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ)
    (hOdd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (hPlateau : ∀ x ∈ tsupport θ, (χ : E₀ → ℝ) =ᶠ[𝓝 x] fun _ : E₀ => (1 : ℝ)) :
    let U := (chartAt E₀ c).target
    let S := orthonormalMetricDirection
    let b := normalizedChartMetric B c
    let h (n : ℕ) := normalizedChartPerturbation B (g n) c
    let P := windowedWeylLeftSymbol θ β R hAmp
    let f (n : ℕ) (i : I) := (symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ n i.val
    ∃ z w : ℕ → RealEnergyField I,
      (∀ n i, (z n).val i = f n i) ∧
      (∀ n i x, (w n).val i x = (-Complex.I) * firstOrderAction P (f n i) x) ∧
      (∀ n i, tsupport ((w n).val i : E₀ → ℂ) ⊆ tsupport θ) ∧
      ∀ n, (∫ x in U, ∑ i : I, conj ((-Complex.I) * firstOrderAction P (f n i) x) *
        Complex.ofReal (deriv (deriv (fun t : ℝ =>
          coordinateDensityEuler S (fun y => b y + t • h n y) x i)) 0)).re =
        ∫ x in tsupport θ, coordinateActionThirdVariationDensity S b
          (fun y i => ((z n).val i y).re) (fun y i => ((w n).val i y).re) x := by
  intro U S b h P f
  have hU : IsOpen U := (chartAt E₀ c).open_target
  have hb : ContDiffOn ℝ ∞ b U := contDiffOn_normalizedChartMetric B hB c
  have hh (n : ℕ) : ContDiffOn ℝ ∞ (h n) U := (contDiffOn_normalizedChartMetric (g n) (hg n) c).sub hb
  have hdet (x : E₀) (hx : x ∈ U) : (assembleMetricComponents S (b x)).det ≠ 0 := by
    change (assembledCoordinateMetric S b x).det ≠ 0
    rw [show assembledCoordinateMetric S b =
        metricComponents (ManifoldMetricTransition.coordinateBilinear B c) from
      assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric c]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hx
  let F (n : ℕ) := chartMetricCutoffTest hU (h n) (hh n) (χ : E₀ → ℝ)
    (test_smooth χ) hχ (test_compactSupport χ)
  have hF (n : ℕ) (i : I) : (F n).val i = f n i :=
    normalizedChartCutoffTest_eq_weylPerturbation B g hB hg c χ hχ n i (hh n)
  have hFreal (n : ℕ) (i : I) (x : E₀) : conj ((F n).val i x) = (F n).val i x :=
    Complex.conj_ofReal _
  obtain ⟨A, hA, hAS, _, hAR⟩ := exists_windowedWeylCompactMatrixTest θ β R hAmp hDir hθβ
    hθ hθc hβ hReal hOdd (ι := I)
  let z (n : ℕ) : RealEnergyField I := ⟨(F n).val, hFreal n⟩
  let w (n : ℕ) : RealEnergyField I := ⟨((-Complex.I) • A (F n)).val, hAR (F n) (hFreal n)⟩
  have hw (n : ℕ) (i : I) (x : E₀) : (w n).val i x = (-Complex.I) * firstOrderAction P (f n i) x := by
    change (-Complex.I) * (A (F n)).val i x = _
    rw [hA, hF]
  have hws (n : ℕ) (i : I) : tsupport ((w n).val i : E₀ → ℂ) ⊆ tsupport θ := by
    change tsupport (fun x : E₀ => (-Complex.I) • (A (F n)).val i x) ⊆ tsupport θ
    exact (tsupport_smul_subset_right (fun _ : E₀ => -Complex.I) _).trans (hAS (F n) i)
  have hθU : tsupport θ ⊆ U := by
    intro x hx
    apply hχ
    apply subset_tsupport (χ : E₀ → ℝ)
    change (χ : E₀ → ℝ) x ≠ 0
    rw [(hPlateau x hx).eq_of_nhds]
    exact one_ne_zero
  have hEq (n : ℕ) (x : E₀) (hx : x ∈ tsupport θ) :
      h n =ᶠ[𝓝 x] fun y i => ((z n).val i y).re := by
    filter_upwards [hPlateau x hx] with y hy
    funext i
    change h n y i = (Complex.ofReal ((χ : E₀ → ℝ) y * h n y i)).re
    rw [Complex.ofReal_re, hy, one_mul]
  refine ⟨z, w, hF, hw, hws, fun n => ?_⟩
  have hThird := setIntegral_quadraticEuler_pair_eq_thirdVariation_of_germ
    S b (h n) (z n) (w n) hU hθc.isCompact hθU hb hdet (hws n) (hEq n)
  simpa only [hw] using hThird

end Burnett.V03.Palatini
