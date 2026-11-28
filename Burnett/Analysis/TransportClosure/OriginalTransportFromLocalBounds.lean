import Burnett.Analysis.TransportClosure.OriginalIntrinsicPhysicalReflection
import Burnett.Analysis.TransportClosure.C04OddChartPartition
import Burnett.Analysis.TransportPatches.TransportNumericalLimit

/-! From the paper's local two-scale inequality to global transport for
the particular measure of the original quadratic construction. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.C04

open Filter Function MeasureTheory Set Bundle Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open scoped ContDiff ENNReal Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The local estimate is imposed on the restriction of the same measure
in each chart. Its first coefficient is uniform across the two scales.
The geometric and measure-theoretic steps yield the full real transport
class once the original sequence supplies this estimate. -/
theorem originalTransport_of_chartwise_twoScale_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hLocalBound : ∀ (c : M) (b : CotangentBundle M → ℝ), IsDegreeOneTransportTest b →
      IsAntipodallyOdd b → HasCompactTransportBaseSupportIn b (chartAt E c).source →
      let I := ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source},
        chartHamiltonDerivative c B hSig.isNondegenerate b p.val ∂μ
      ∃ C α β δ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D F ℓ₀ : ℝ, 0 < ℓ₀ ∧
          ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + F * ℓ) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hSig.isNondegenerate a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hSig.isNondegenerate a p.val ∂μ) = 0 := by
  have hEven := originalIntrinsicPhysicalContraction_antipodal
    r B g hB hg hSig hsG hnG hconv hb hv σ hσ A μ hA hPhysical
  apply transport_of_chartwise_oddTests_of_nullMeasure r B hB hSig.isNondegenerate
    hSig.isSymmetric μ hNull hFinite hEven
  intro c b hbTest hOdd hSupport
  obtain ⟨C, α, β, δ₀, hα, hβ, hδ₀, hBound⟩ := hLocalBound c b hbTest hOdd hSupport
  exact residual_eq_zero_of_two_scale_bound _ C α β δ₀ hα hβ hδ₀ hBound

end Burnett.C04
