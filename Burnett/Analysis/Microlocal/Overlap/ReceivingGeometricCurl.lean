import Burnett.Analysis.Microlocal.Overlap.ReceivingCovariantCurl

/-! The chart row of the localized geometric covariant curl includes all
three connection corrections in each of its two differentiations. -/

set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open BackgroundConnection ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.Geometry.UnitCosphere (projection)
open Burnett.F05.CoordinateCurl (axis curlRowCoefficients curlRowDirections curlRowInputs)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (coeffMul firstOrderRow)
open Burnett.Microlocal.CurlDensity (JetSlot CurlSlot curlMatrix)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private def tensorSlot (k : JetSlot) : Fin 3 → Index := ![k.1, k.2.1, k.2.2]

private def replaceTensorSlot (k : JetSlot) (l : Index) : Fin 3 → JetSlot :=
  ![(l, k.2), (k.1, l, k.2.2), (k.1, k.2.1, l)]

private def curlDerivativeIndex (s : CurlSlot) : Fin 2 → Index := ![s.1, s.2.1]

private def curlConnectionSign : Fin 2 → ℝ := ![-1, 1]

abbrev CurlConnectionTerm := Fin 2 × (Fin 3 × Index)

def receivingCurlConnectionInput (s : CurlSlot) (t : CurlConnectionTerm) : JetSlot :=
  replaceTensorSlot (curlRowInputs s.1 s.2.1 s.2.2 t.1) t.2.2 t.2.1

/-- The correction to a coordinate partial derivative on all three
covariant indices of a localized tensor. -/
def chartCovariantThreeCorrection (r : Metric (M := M)) (c : AtlasChart M)
    (d : Index) (k : JetSlot) (u : JetSlot → SchwartzMap E ℂ) (x : E) : ℂ :=
  ∑ t : Fin 3 × Index, (computedConnection (fixedForm r.inner c) x t.2 d (tensorSlot k t.1) : ℂ) *
    u (replaceTensorSlot k t.2 t.1) x

def chartCovariantThreeDerivative (r : Metric (M := M)) (c : AtlasChart M)
    (d : Index) (k : JetSlot) (u : JetSlot → SchwartzMap E ℂ) (x : E) : ℂ :=
  SchwartzMap.pderivCLM ℂ (axis d) (u k) x - chartCovariantThreeCorrection r c d k u x

variable [SecondCountableTopology M]

def receivingCurlConnectionCoefficient (r : Metric (M := M)) (c : AtlasChart M)
    (θ : D) (hθc : tsupport (θ : E → ℝ) ⊆ c.chart.target) (s : CurlSlot) (t : CurlConnectionTerm) : D :=
  let d := curlDerivativeIndex s t.1
  let b := tensorSlot (curlRowInputs s.1 s.2.1 s.2.2 t.1) t.2.1
  let Γ := computedConnection (fixedForm r.inner c)
  have hΓ : ContDiffOn ℝ ∞ Γ c.chart.target :=
    fixedForm_connection_smooth r.inner (isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) c
  have hΓ_t : ContDiffOn ℝ ∞ (fun x => Γ x t.2.2 d b) c.chart.target :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ t.2.2) d) b
  ⟨fun x => (θ : E → ℝ) x * (curlConnectionSign t.1 * Γ x t.2.2 d b),
    contDiff_test_mul_local c.chart.open_target (test_smooth θ) hθc (contDiffOn_const.mul hΓ_t),
    (test_compactSupport θ).mul_right⟩

/-- The row is exactly the antisymmetrization of the auxiliary connection
acting on the localized three-covariant tensor. -/
theorem receivingGeometricCurlRow_apply (r : Metric (M := M)) (c : AtlasChart M)
    (θ : D) (hθc : tsupport (θ : E → ℝ) ⊆ c.chart.target)
    (s : CurlSlot) (u : JetSlot → SchwartzMap E ℂ) (x : E) :
    firstOrderRow (curlRowCoefficients θ) (curlRowDirections s.1 s.2.1)
      (curlRowInputs s.1 s.2.1 s.2.2) (receivingCurlConnectionCoefficient r c θ hθc s)
      (receivingCurlConnectionInput s) u x =
    ((θ : E → ℝ) x : ℂ) *
      (chartCovariantThreeDerivative r c s.1 (s.2.1, s.2.2) u x -
        chartCovariantThreeDerivative r c s.2.1 (s.1, s.2.2) u x) := by
  have hEval {I : Type} [Fintype I] (F : I → SchwartzMap E ℂ) : (∑ j, F j) x = ∑ j, F j x :=
    map_sum (SchwartzMap.delta ℂ ℂ x) F Finset.univ
  let a := ((θ : E → ℝ) x : ℂ)
  rw [firstOrderRow, SchwartzMap.add_apply, hEval, hEval, Fin.sum_univ_two, Fintype.sum_prod_type]
  have hLower (d : Fin 2) :
      (∑ t : Fin 3 × Index, coeffMul (receivingCurlConnectionCoefficient r c θ hθc s (d, t))
        (u (receivingCurlConnectionInput s (d, t))) x) =
        (a * (curlConnectionSign d : ℂ)) * chartCovariantThreeCorrection r c (curlDerivativeIndex s d)
          (curlRowInputs s.1 s.2.1 s.2.2 d) u x := by
    rw [chartCovariantThreeCorrection, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    change (((θ : E → ℝ) x * (curlConnectionSign d * computedConnection (fixedForm r.inner c) x t.2
        (curlDerivativeIndex s d) (tensorSlot (curlRowInputs s.1 s.2.1 s.2.2 d) t.1)) : ℝ) : ℂ) *
      u (receivingCurlConnectionInput s (d,t)) x = _
    simp only [a, Complex.ofReal_mul, receivingCurlConnectionInput, mul_assoc]
  simp only [hLower, Fin.sum_univ_two, chartCovariantThreeDerivative]
  change a * SchwartzMap.pderivCLM ℂ (axis s.1) (u (s.2.1, s.2.2)) x +
    ((-(θ : E → ℝ) x : ℝ) : ℂ) * SchwartzMap.pderivCLM ℂ (axis s.2.1) (u (s.1, s.2.2)) x +
    (a * ((-1 : ℝ) : ℂ) * chartCovariantThreeCorrection r c s.1 (s.2.1, s.2.2) u x +
      a * ((1 : ℝ) : ℂ) * chartCovariantThreeCorrection r c s.2.1 (s.1, s.2.2) u x) = _
  rw [Complex.ofReal_neg, Complex.ofReal_neg, Complex.ofReal_one]
  change a * _ + -a * _ + (a * -1 * _ + a * 1 * _) = _
  ring

variable [MeasurableSpace M] [BorelSpace M]

theorem fixedVolumeGeometricCurl_negativeEnergy_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (θ : D) (hθc : tsupport (θ : E → ℝ) ⊆ c.chart.target)
    (hθ : ∀ x ∈ tsupport (χ : E → ℝ), (θ : E → ℝ) x = 1) (s : CurlSlot) :
    Tendsto (fun n => negativeEnergy (firstOrderRow (curlRowCoefficients θ)
      (curlRowDirections s.1 s.2.1) (curlRowInputs s.1 s.2.1 s.2.2)
      (receivingCurlConnectionCoefficient r c θ hθc s) (receivingCurlConnectionInput s)
      (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n))) atTop (𝓝 0) :=
  fixedVolumeCovariantCurl_negativeEnergy_tendsto_zero r B g hB hg hn hconv hb c χ hχ θ hθ s
    (receivingCurlConnectionCoefficient r c θ hθc s) (receivingCurlConnectionInput s)

variable [T2Space M]

/-- The genuine geometric curl constrains the existing intrinsic jet
covariance on the same cutoff, with an exterior coefficient plateau in the same chart. -/
theorem original_receiving_geometricCurl_kernel
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      curlMatrix (atlasChartUnitCovector c p) * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ z : JetSlot → ℂ, curlMatrix (atlasChartUnitCovector c p) *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ z) = 0 := by
  have hχc : tsupport (χ : E → ℝ) ⊆ c.chart.target :=
    hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
  obtain ⟨L, _, _, hLc, θ, hs, hc, hθL, _, hOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart (test_compactSupport χ) c.chart.open_target hχc
  let θ₀ : D := ⟨θ, hs, hc⟩
  have hθc : tsupport (θ₀ : E → ℝ) ⊆ c.chart.target := hθL.trans hLc
  exact original_receiving_covariant_curl_kernel r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA
    c K hK hKc χ hχ θ₀ hOne (receivingCurlConnectionCoefficient r c θ₀ hθc) receivingCurlConnectionInput

end Burnett.Microlocal.Overlap
