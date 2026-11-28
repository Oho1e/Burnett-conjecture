import Burnett.Analysis.TransportClosure.HamiltonCosphereIntegrability
import Burnett.Geometry.Cotangent.CompactTestPartition

/-! A finite smooth base partition turns the same-measure chartwise odd
transport identities into the global C04 identity. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.C04

open Bundle Filter Function MeasureTheory Set Burnett.Geometry
open Burnett.RicciSymbol (Covector)
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open CotangentAngularExtension
open UnitNullAngular (Phase chartPunctured)
open UnitCosphere (Cosphere antipode coe_mem_punctured hamiltonian projection)
open CotangentTests (exists_finite_smooth_cutoffs_on_compact)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open scoped BigOperators ContDiff ENNReal Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Compact support in the base of the actual punctured cotangent bundle test. -/
def HasCompactTransportBaseSupportIn (a : CotangentBundle M → ℝ) (U : Set M) : Prop :=
  ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
    ∀ p ∈ puncturedCotangent, p.proj ∉ K → a p = 0

/-- Pull back a smooth scalar cutoff from the base and multiply the actual test. -/
def localizeTransportTest (ρ : M → ℝ) (a : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  ρ p.proj * a p

private theorem localizeTransportTest_eq_zero_of_notMem_tsupport (ρ : M → ℝ)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) (hp : p.proj ∉ tsupport ρ) :
    localizeTransportTest ρ a p = 0 := by
  rw [localizeTransportTest, image_eq_zero_of_notMem_tsupport hp, zero_mul]

theorem IsDegreeOneTransportTest.localize {a : CotangentBundle M → ℝ}
    (ha : IsDegreeOneTransportTest a) {ρ : M → ℝ} (hsm : ContMDiff Model 𝓘(ℝ) ∞ ρ)
    (hc : HasCompactSupport ρ) : IsDegreeOneTransportTest (localizeTransportTest ρ a) := by
  have hπ : ContMDiff CotangentModelWithCorners Model ∞ (fun p : CotangentBundle M => p.proj) :=
    Bundle.contMDiff_proj (CotangentFiber (M := M))
  refine ⟨(hsm.comp hπ).contMDiffOn.mul ha.1, ?_, tsupport ρ, hc, ?_⟩
  · intro p hp t ht
    rw [localizeTransportTest, cotangentScale_projection, ha.2.1 p hp t ht,
      localizeTransportTest, mul_left_comm]
  · intro p _ hp
    exact localizeTransportTest_eq_zero_of_notMem_tsupport ρ a p hp

theorem IsAntipodallyOdd.localize {a : CotangentBundle M → ℝ} (ha : IsAntipodallyOdd a)
    (ρ : M → ℝ) : IsAntipodallyOdd (localizeTransportTest ρ a) := by
  intro p hp
  simp only [localizeTransportTest, cotangentScale_projection, ha p hp, mul_neg]

theorem hasCompactTransportBaseSupportIn_localize (a : CotangentBundle M → ℝ)
    {ρ : M → ℝ} (hc : HasCompactSupport ρ) {U : Set M} (hρ : tsupport ρ ⊆ U) :
    HasCompactTransportBaseSupportIn (localizeTransportTest ρ a) U :=
  ⟨tsupport ρ, hc, hρ, fun p _ hp => localizeTransportTest_eq_zero_of_notMem_tsupport ρ a p hp⟩

variable [T2Space M]

/-- A fixed global odd test is a finite sum of genuine chart-supported odd tests
throughout the punctured cotangent bundle. -/
theorem exists_finite_localized_odd_transportTests
    (a : CotangentBundle M → ℝ) (ha : IsDegreeOneTransportTest a) (ho : IsAntipodallyOdd a) :
    ∃ (n : ℕ) (c : Fin n → M) (ρ : Fin n → M → ℝ),
      (∀ k,
        IsDegreeOneTransportTest (localizeTransportTest (ρ k) a) ∧
        IsAntipodallyOdd (localizeTransportTest (ρ k) a) ∧
        HasCompactTransportBaseSupportIn (localizeTransportTest (ρ k) a) (chartAt E (c k)).source) ∧
      ∀ p ∈ puncturedCotangent, a p = ∑ k, localizeTransportTest (ρ k) a p := by
  obtain ⟨K, hK, hzero⟩ := ha.2.2
  let U (c : M) := (chartAt E c).source
  have hcover : K ⊆ ⋃ c, U c := fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source E x⟩
  obtain ⟨n, c, ρ, V, _, hKV, hρ, hsum⟩ :=
    exists_finite_smooth_cutoffs_on_compact U (fun c => (chartAt E c).open_source) hK hcover
  refine ⟨n, c, ρ, ?_, ?_⟩
  · intro k
    obtain ⟨hsm, hc, hs, _⟩ := hρ k
    exact ⟨ha.localize hsm hc, ho.localize (ρ k),
      hasCompactTransportBaseSupportIn_localize a hc hs⟩
  · intro p hp
    simp only [localizeTransportTest, ← Finset.sum_mul]
    by_cases h : p.proj ∈ K
    · rw [hsum p.proj (hKV h), one_mul]
    · rw [hzero p hp h, mul_zero]

omit [T2Space M] in
/-- Equality of actual tests with a finite sum on the punctured bundle gives
equality of their Hamilton derivatives at every nonzero cotangent point. -/
theorem basePointHamiltonDerivative_eq_sum_of_punctured {ι : Type*} [Fintype ι]
    (B : Field (M := M)) (hn : IsNondegenerate B)
    (a : CotangentBundle M → ℝ) (b : ι → CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (hb : ∀ i, ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (b i) puncturedCotangent)
    (hEq : ∀ p ∈ puncturedCotangent, a p = ∑ i, b i p)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) :
    basePointHamiltonDerivative B hn a p = ∑ i, basePointHamiltonDerivative B hn (b i) p := by
  let c := p.proj
  let z := cotangentChart c p
  let aChart (f : CotangentBundle M → ℝ) (x : E) (ξ : Covector) := f (cotangentChartInverse c (x, ξ))
  let A := chartHamiltonian c B hn
  have hz : z ∈ chartPunctured c :=
    cotangentChart_mem_chartPunctured c p (mem_chart_source E c) hp
  have hneb := (isOpen_chartPunctured c).mem_nhds hz
  have hA : DifferentiableAt ℝ (uncurry (aChart a)) z :=
    ((contDiffOn_cotangentChartTest_joint c a ha).contDiffAt hneb).differentiableAt (by simp)
  have hD (i : ι) : DifferentiableAt ℝ (uncurry (aChart (b i))) z :=
    ((contDiffOn_cotangentChartTest_joint c (b i) (hb i)).contDiffAt hneb).differentiableAt (by simp)
  have hg : uncurry (aChart a) =ᶠ[𝓝 z] fun q => ∑ i, uncurry (aChart (b i)) q := by
    filter_upwards [hneb] with q hq
    exact hEq _ (cotangentChartInverse_mapsTo_punctured c hq)
  have hsum : HasFDerivAt (fun q => ∑ i, uncurry (aChart (b i)) q)
      (∑ i, fderiv ℝ (uncurry (aChart (b i))) z) z :=
    HasFDerivAt.fun_sum fun i _ => (hD i).hasFDerivAt
  change canonicalBracket A (aChart a) z.1 z.2 = ∑ i, canonicalBracket A (aChart (b i)) z.1 z.2
  rw [canonicalBracket_eq_fderiv A (aChart a) z hA, hg.fderiv_eq, hsum.fderiv,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (canonicalBracket_eq_fderiv A (aChart (b i)) z (hD i)).symm

/-- A genuine chart-supported test has the same global derivative integral as
its chart derivative integrated over the actual chart part of the same measure. -/
theorem integral_basePointHamiltonDerivative_eq_chart_restrict (r : Metric (M := M))
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (μ : Measure (Cosphere r)) (c : M) (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (hSupp : HasCompactTransportBaseSupportIn a (chartAt E c).source) :
    (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) =
      ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source},
        chartHamiltonDerivative c B hn a p.val ∂μ := by
  obtain ⟨K, hK, hKU, hzero⟩ := hSupp
  let V : Set (Cosphere r) := {p | p.val.proj ∈ (chartAt E c).source}
  have hV : MeasurableSet V := ((chartAt E c).open_source.preimage
    (UnitCosphere.continuous_projection r)).measurableSet
  change _ = ∫ p in V, chartHamiltonDerivative c B hn a p.val ∂μ
  rw [← integral_indicator hV]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  have hp := coe_mem_punctured r p
  by_cases h : p ∈ V
  · rw [indicator_of_mem h]
    exact basePointHamiltonDerivative_eq_chart B hB hn hs a ha c p.val hp h
  · rw [indicator_of_notMem h]
    exact basePointHamiltonDerivative_eq_zero_of_outside_base r B hn a hK.isClosed hzero
      p (fun hpK => h (hKU hpK))

/-- The local odd identities use the restriction of the original cosphere
measure in each chart. Smoothly cutting the original test and differentiating the
finite sum gives the global odd identity on that same measure. -/
theorem transport_of_chartwise_oddTests (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B) (μ : Measure (Cosphere r))
    (hLocal : ∀ (c : M) (b : CotangentBundle M → ℝ), IsDegreeOneTransportTest b →
      IsAntipodallyOdd b → HasCompactTransportBaseSupportIn b (chartAt E c).source →
      ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source},
        chartHamiltonDerivative c B hn b p.val ∂μ = 0)
    (hIntegrable : ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ) :
    ∀ a, IsDegreeOneTransportTest a → IsAntipodallyOdd a →
      ∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ = 0 := by
  intro a ha ho
  obtain ⟨n, c, ρ, hl, hEq⟩ := exists_finite_localized_odd_transportTests a ha ho
  let b (k : Fin n) := localizeTransportTest (ρ k) a
  have hb (k : Fin n) : IsDegreeOneTransportTest (b k) := (hl k).1
  have hS (p : Cosphere r) :
      basePointHamiltonDerivative B hn a p.val = ∑ k, basePointHamiltonDerivative B hn (b k) p.val :=
    basePointHamiltonDerivative_eq_sum_of_punctured B hn a b ha.1 (fun k => (hb k).1)
      hEq p.val (coe_mem_punctured r p)
  have hi (k : Fin n) : Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn (b k) p.val) μ :=
    hIntegrable (b k) (hb k)
  calc
    _ = ∫ p : Cosphere r, ∑ k, basePointHamiltonDerivative B hn (b k) p.val ∂μ :=
      integral_congr_ae (ae_of_all μ hS)
    _ = ∑ k, ∫ p : Cosphere r, basePointHamiltonDerivative B hn (b k) p.val ∂μ :=
      integral_finset_sum Finset.univ (fun k _ => hi k)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [integral_basePointHamiltonDerivative_eq_chart_restrict r B hB hn hs μ (c k)
        (b k) (hb k).1 (hl k).2.2]
      exact hLocal (c k) (b k) (hb k) (hl k).2.1 (hl k).2.2

/-- With antipodal invariance of the same measure, the chartwise odd identities
also give the global identity for every real degree-one test. -/
theorem transport_of_chartwise_oddTests_of_antipodalMeasure
    (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B) (μ : Measure (Cosphere r))
    (hEven : μ.map (antipode r) = μ)
    (hLocal : ∀ (c : M) (b : CotangentBundle M → ℝ), IsDegreeOneTransportTest b →
      IsAntipodallyOdd b → HasCompactTransportBaseSupportIn b (chartAt E c).source →
      ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source},
        chartHamiltonDerivative c B hn b p.val ∂μ = 0)
    (hIntegrable : ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) = 0 :=
  transport_of_oddTests_of_antipodalMeasure r B hn μ hEven
    (transport_of_chartwise_oddTests r B hB hn hs μ hLocal hIntegrable) hIntegrable

/-- The global identity and its integrability for the original, antipodally
invariant unit-null measure with finite mass over compact base sets. -/
theorem transport_of_chartwise_oddTests_of_nullMeasure
    (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian B hn p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hEven : μ.map (antipode r) = μ)
    (hLocal : ∀ (c : M) (b : CotangentBundle M → ℝ), IsDegreeOneTransportTest b →
      IsAntipodallyOdd b → HasCompactTransportBaseSupportIn b (chartAt E c).source →
      ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source},
        chartHamiltonDerivative c B hn b p.val ∂μ = 0) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) = 0 :=
  transport_of_chartwise_oddTests_of_antipodalMeasure r B hB hn hs μ hEven hLocal
    (integrable_basePointHamiltonDerivative r B hB hn hs μ hNull hFinite)

end Burnett.C04
