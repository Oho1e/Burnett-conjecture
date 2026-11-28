import Burnett.Analysis.TransportClosure.C04IntrinsicHamiltonOverlap
import Burnett.Analysis.TransportClosure.HamiltonCompactBaseIntegrability

/-! Chartwise continuity of the actual Hamiltonian derivative and integrability
against the physical measure concentrated on the auxiliary unit null section. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.C04

open Filter Function MeasureTheory Set Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere coe_mem_punctured hamiltonian projection antipode)
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitNullAngular (Phase chartPunctured)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff ENNReal Manifold Topology BigOperators

open private basePartial_eq_fderiv momentumPartial_eq_fderiv from Burnett.Analysis.TransportClosure.C04IntrinsicHamiltonOverlap

local notation "E" => CoordinateSpace

/-- The local bracket is continuous wherever both genuine chart functions are smooth. -/
theorem continuousOn_canonicalBracket {U : Set Phase} (hU : IsOpen U)
    {P a : E → Covector → ℝ}
    (hP : ContDiffOn ℝ ∞ (uncurry P) U) (ha : ContDiffOn ℝ ∞ (uncurry a) U) :
    ContinuousOn (fun z : Phase => canonicalBracket P a z.1 z.2) U := by
  have hbase {f : E → Covector → ℝ} (hf : ContDiffOn ℝ ∞ (uncurry f) U) (i : Index) :
      ContinuousOn (fun z : Phase => basePartial i f z.1 z.2) U := by
    have hD := hf.continuousOn_fderiv_of_isOpen hU (by simp : 1 ≤ (∞ : WithTop ℕ∞))
    exact (hD.clm_apply (continuousOn_const (c := (coordinateBasis i, (0 : Covector))))).congr
      (fun z hz => basePartial_eq_fderiv
        (hf.differentiableOn (by simp) z hz |>.differentiableAt (hU.mem_nhds hz)) i)
  have hmomentum {f : E → Covector → ℝ} (hf : ContDiffOn ℝ ∞ (uncurry f) U) (i : Index) :
      ContinuousOn (fun z : Phase => momentumPartial i f z.1 z.2) U := by
    have hD := hf.continuousOn_fderiv_of_isOpen hU (by simp : 1 ≤ (∞ : WithTop ℕ∞))
    exact (hD.clm_apply (continuousOn_const (c := ((0 : E), Pi.single i (1 : ℝ))))).congr
      (fun z hz => momentumPartial_eq_fderiv
        (hf.differentiableOn (by simp) z hz |>.differentiableAt (hU.mem_nhds hz)) i)
  exact continuousOn_finset_sum Finset.univ (fun i _ =>
    ((hmomentum hP i).mul (hbase ha i)).sub ((hbase hP i).mul (hmomentum ha i)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Though the defining chart index varies with the base point, the actual
Hamiltonian derivative is continuous on the unit cosphere. -/
theorem continuous_basePointHamiltonDerivative (r : Metric (M := M))
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) :
    Continuous (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  let c := p.val.proj
  let V : Set (Cosphere r) := Subtype.val ⁻¹' cotangentSource c
  have hV : IsOpen V := (isOpen_cotangentSource c).preimage continuous_subtype_val
  have hpV : p ∈ V := mem_chart_source E c
  let P := chartHamiltonian c B hn
  let A (x : E) (ξ : Covector) := a (cotangentChartInverse c (x, ξ))
  have hP : ContDiffOn ℝ ∞ (uncurry P) (chartPunctured c) :=
    (contDiffOn_chartHamiltonian_joint c B hB hn hs).mono (fun _ hz => ⟨hz.1, trivial⟩)
  have hA : ContDiffOn ℝ ∞ (uncurry A) (chartPunctured c) :=
    contDiffOn_cotangentChartTest_joint c a ha
  have hChart : ContinuousOn (fun q : Cosphere r => cotangentChart c q.val) V :=
    (contMDiffOn_cotangentChart c).continuousOn.comp continuous_subtype_val.continuousOn (fun _ hq => hq)
  have hBracket := (continuousOn_canonicalBracket (isOpen_chartPunctured c) hP hA).comp hChart
    (fun q hq => cotangentChart_mem_chartPunctured c q.val hq (coe_mem_punctured r q))
  have hOn : ContinuousOn (fun q : Cosphere r => basePointHamiltonDerivative B hn a q.val) V :=
    hBracket.congr (fun q hq =>
      basePointHamiltonDerivative_eq_chart B hB hn hs a ha c q.val (coe_mem_punctured r q) hq)
  exact hOn.continuousAt (hV.mem_nhds hpV)

variable [T2Space M]

/-- Compact base support and null concentration are sufficient for actual
Bochner integrability of every admitted transport test. -/
theorem integrable_basePointHamiltonDerivative (r : Metric (M := M))
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (μ : Measure (Cosphere r)) (hNull : μ {p | hamiltonian B hn p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (a : CotangentBundle M → ℝ) (ha : IsDegreeOneTransportTest a) :
    Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ := by
  obtain ⟨K, hK, hZero⟩ := ha.2.2
  exact integrable_of_nullSupport_of_compactBase r B hB hn hs μ hNull hFinite _
    (continuous_basePointHamiltonDerivative r B hB hn hs a ha.1) K hK
    (fun p hp => basePointHamiltonDerivative_eq_zero_of_outside_base r B hn a hK.isClosed hZero p hp)

/-- With the actual support, local mass and reflection properties, the odd
identity suffices for the genuine full class of transport tests. -/
theorem transport_of_oddTests_of_nullMeasure (r : Metric (M := M))
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (μ : Measure (Cosphere r)) (hNull : μ {p | hamiltonian B hn p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hEven : μ.map (antipode r) = μ)
    (hOdd : ∀ a, IsDegreeOneTransportTest a → IsAntipodallyOdd a →
      ∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ = 0) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) = 0 :=
  transport_of_oddTests_of_antipodalMeasure r B hn μ hEven hOdd
    (integrable_basePointHamiltonDerivative r B hB hn hs μ hNull hFinite)

end Burnett.C04
