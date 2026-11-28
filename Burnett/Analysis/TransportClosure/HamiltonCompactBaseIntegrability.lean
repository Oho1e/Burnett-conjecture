import Burnett.Analysis.TransportClosure.C04HamiltonChartRegularity
import Burnett.Analysis.TransportClosure.AntipodalTransportReduction

/-! Compact base support of genuine Hamilton derivatives and integrability on the null measure. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.C04

open Filter Function MeasureTheory Set Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere coe_mem_punctured hamiltonian projection isClosed_unitCosphere)
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitNullAngular (Phase chartPunctured)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff ENNReal Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A scalar test vanishing away from a closed base set has zero actual
canonical derivative there. The two derivatives only use punctured germs. -/
theorem chartHamiltonDerivative_eq_zero_of_outside_base
    (c : M) (B : Field (M := M)) (hn : IsNondegenerate B) (a : CotangentBundle M → ℝ)
    {K : Set M} (hK : IsClosed K) (hZero : ∀ q ∈ puncturedCotangent, q.proj ∉ K → a q = 0)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hc : p.proj ∈ (chartAt E c).source)
    (hOut : p.proj ∉ K) : chartHamiltonDerivative c B hn a p = 0 := by
  let e := chartAt E c
  let x := e p.proj
  let ξ := cotangentCoords c p
  have hx : x ∈ e.target := e.mapsTo hc
  have hξ : ξ ≠ 0 := cotangentCoords_ne_zero_of_punctured c p hc hp
  have hOut' : e.symm x ∉ K := by simpa only [x, e.left_inv hc] using hOut
  have hC : ContinuousAt (e.symm : E → M) x := (e.continuousOn_symm x hx).continuousAt (e.open_target.mem_nhds hx)
  have hN : ∀ᶠ y in 𝓝 x, e.symm y ∉ K := hC.eventually (hK.isOpen_compl.mem_nhds hOut')
  let f (y : E) (η : Covector) := a (cotangentChartInverse c (y, η))
  have hBase : (fun y => f y ξ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [e.open_target.mem_nhds hx, hN] with y hy hNy
    exact hZero _ (cotangentChartInverse_mapsTo_punctured c ⟨hy, hξ⟩) hNy
  have hFreq : f x =ᶠ[𝓝 ξ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with η hη
    exact hZero _ (cotangentChartInverse_mapsTo_punctured c ⟨hx, hη⟩) hOut'
  change canonicalBracket (chartHamiltonian c B hn) f x ξ = 0
  simp only [canonicalBracket, basePartial, momentumPartial, hBase.fderiv_eq, hFreq.fderiv_eq,
    fderiv_const_apply, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, Finset.sum_const_zero]

/-- The derivative of a compactly based test is zero off the same base set
throughout the auxiliary unit section. -/
theorem basePointHamiltonDerivative_eq_zero_of_outside_base
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B) (a : CotangentBundle M → ℝ)
    {K : Set M} (hK : IsClosed K) (hZero : ∀ q ∈ puncturedCotangent, q.proj ∉ K → a q = 0)
    (p : Cosphere r) (hp : projection p ∉ K) : basePointHamiltonDerivative B hn a p.val = 0 :=
  chartHamiltonDerivative_eq_zero_of_outside_base p.val.proj B hn a hK hZero p.val
    (coe_mem_punctured r p) (mem_chart_source E p.val.proj) hp

variable [T2Space M]

/-- A continuous compactly based scalar is integrable for the positive
physical cosphere measure with the stated null support and compact-base mass. -/
theorem integrable_of_nullSupport_of_compactBase
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (hs : IsSymmetric B) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian B hn p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (f : Cosphere r → ℝ) (hC : Continuous f) (K : Set M) (hK : IsCompact K)
    (hZero : ∀ p, projection p ∉ K → f p = 0) : Integrable f μ := by
  letI : T2Space (CotangentBundle M) := cotangentBundle_t2Space
  let e : Cosphere r → CotangentBundle M := Subtype.val
  let S : Set (CotangentBundle M) := {p ∈ cotangentUnitNull r B hn | p.proj ∈ K}
  let T := e ⁻¹' S
  have hS : IsCompact S := isCompact_cotangentUnitNull_over r B hB hn hs hK
  have hEmb : Topology.IsClosedEmbedding e := (isClosed_unitCosphere r).isClosedEmbedding_subtypeVal
  have hT : IsCompact T := hEmb.isProperMap.isCompact_preimage hS
  have hTm := hT.isClosed.measurableSet
  have hTK : T ⊆ projection ⁻¹' K := fun _ hp => hp.2
  have hTFin : μ T < ⊤ := (measure_mono hTK).trans_lt (hFinite K hK)
  have hMeasure : IsFiniteMeasure (μ.restrict T) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  letI := hMeasure
  obtain ⟨C, hBound⟩ := (hT.image hC).isBounded.exists_norm_le
  have hIntegrable : IntegrableOn f T μ := by
    refine (integrable_const C).mono' hC.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := μ) hTm] with p hp
    exact hBound (f p) (mem_image_of_mem f hp)
  have hAE : ∀ᵐ p ∂μ, hamiltonian B hn p = 0 := by
    rw [ae_iff]
    exact hNull
  refine (hIntegrable.integrable_indicator hTm).congr ?_
  filter_upwards [hAE] with p hp
  by_cases hMem : projection p ∈ K
  · change dualEnergy B hn p.val / 2 = 0 at hp
    have hP := (div_eq_zero_iff.mp hp).resolve_right (by norm_num)
    have hIn : p ∈ T := ⟨⟨p.property, hP⟩, hMem⟩
    exact indicator_of_mem hIn f
  · rw [indicator_of_notMem (fun h => hMem (hTK h)), hZero p hMem]

end Burnett.C04
