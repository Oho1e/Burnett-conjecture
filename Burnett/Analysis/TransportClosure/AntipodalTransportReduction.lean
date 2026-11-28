import Burnett.Analysis.TransportClosure.HamiltonAntipodalParity

/-! Odd real homogeneous tests on the same actual cosphere measure. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C04

open Function Filter MeasureTheory Set Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere antipode coe_mem_punctured measurableEmbedding_antipode)
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The real test class on the actual punctured cotangent bundle. -/
def IsDegreeOneTransportTest (a : CotangentBundle M → ℝ) : Prop :=
  ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent ∧
    (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) ∧
    ∃ K : Set M, IsCompact K ∧ ∀ p ∈ puncturedCotangent, p.proj ∉ K → a p = 0

def IsAntipodallyOdd (a : CotangentBundle M → ℝ) : Prop :=
  ∀ p ∈ puncturedCotangent, a (cotangentScale (-1) p) = -a p

private theorem cotangentReflection_punctured (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) :
    cotangentScale (-1) p ∈ puncturedCotangent := by
  exact smul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) hp

private theorem contMDiff_cotangentReflection :
    ContMDiff CotangentModelWithCorners CotangentModelWithCorners ∞
      (cotangentScale (-1) : CotangentBundle M → CotangentBundle M) :=
  contMDiff_cotangentScale.comp (contMDiff_const.prodMk contMDiff_id)

theorem IsDegreeOneTransportTest.reflect {a : CotangentBundle M → ℝ} (ha : IsDegreeOneTransportTest a) :
    IsDegreeOneTransportTest (a ∘ cotangentScale (-1)) := by
  obtain ⟨hsm, hdeg, K, hK, hzero⟩ := ha
  refine ⟨hsm.comp contMDiff_cotangentReflection.contMDiffOn (fun p hp => cotangentReflection_punctured p hp),
    ?_, K, hK, ?_⟩
  · intro p hp t ht
    change a (cotangentScale (-1) (cotangentScale t p)) = t * a (cotangentScale (-1) p)
    rw [cotangentScale_mul, mul_comm (-1) t, ← cotangentScale_mul]
    exact hdeg _ (cotangentReflection_punctured p hp) t ht
  · intro p hp hOut
    exact hzero _ (cotangentReflection_punctured p hp) hOut

/-- The genuine odd part, retaining the original scalar normalization. -/
def oddTransportPart (a : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  (a p - a (cotangentScale (-1) p)) / 2

theorem oddTransportPart_odd (a : CotangentBundle M → ℝ) : IsAntipodallyOdd (oddTransportPart a) := by
  intro p _
  have hInv : cotangentScale (-1) (cotangentScale (-1) p) = p := by
    rw [cotangentScale_mul]
    norm_num [cotangentScale_one]
  unfold oddTransportPart
  rw [hInv]
  ring

theorem IsDegreeOneTransportTest.oddPart {a : CotangentBundle M → ℝ} (ha : IsDegreeOneTransportTest a) :
    IsDegreeOneTransportTest (oddTransportPart a) := by
  have hR := ha.reflect
  obtain ⟨hsm, hdeg, K, hK, hzero⟩ := ha
  refine ⟨(hsm.sub hR.1).div_const 2, ?_, K, hK, ?_⟩
  · intro p hp t ht
    have hFlip := hR.2.1 p hp t ht
    change a (cotangentScale (-1) (cotangentScale t p)) = t * a (cotangentScale (-1) p) at hFlip
    unfold oddTransportPart
    rw [hdeg p hp t ht, hFlip]
    ring
  · intro p hp hOut
    unfold oddTransportPart
    rw [hzero p hp hOut, hzero _ (cotangentReflection_punctured p hp) hOut]
    norm_num

private theorem differentiableAt_chartSlices (c : M) (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (x : E) (hx : x ∈ (chartAt E c).target) (ξ : Covector) (hξ : ξ ≠ 0) :
    DifferentiableAt ℝ (fun y : E => a (cotangentChartInverse c (y, ξ))) x ∧
    DifferentiableAt ℝ (fun η : Covector => a (cotangentChartInverse c (x, η))) ξ := by
  let U := phaseTarget c ∩ Prod.snd ⁻¹' ({0}ᶜ : Set Covector)
  have hU : IsOpen U := (isOpen_phaseTarget c).inter (isOpen_compl_singleton.preimage continuous_snd)
  have hq : (x, ξ) ∈ U := ⟨⟨hx, trivial⟩, hξ⟩
  have hMaps : MapsTo (cotangentChartInverse c) U puncturedCotangent := by
    intro z hz hn
    have he := congrArg Prod.snd (cotangentChart_right_inv c hz.1)
    change cotangentCoords c (cotangentChartInverse c z) = z.2 at he
    have hzero : cotangentCoords c (cotangentChartInverse c z) = 0 := by
      funext i
      simp [cotangentCoords, cotangentTrivialization_apply, show (cotangentChartInverse c z).2 = 0 from hn]
    exact hz.2 (he.symm.trans hzero)
  have hM := (ha.comp ((contMDiffOn_cotangentChartInverse c).mono inter_subset_left) hMaps).contMDiffAt
    (hU.mem_nhds hq)
  unfold CoordinatePhaseModel at hM
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hM
  let aChart (z : E × Covector) := a (cotangentChartInverse c z)
  have hD : DifferentiableAt ℝ aChart (x, ξ) :=
    hM.contDiffAt.differentiableAt (by simp)
  have hBase : DifferentiableAt ℝ (fun y : E => (y, ξ)) x :=
    differentiableAt_id.prodMk (differentiableAt_const ξ)
  have hMomentum : DifferentiableAt ℝ (fun η : Covector => (x, η)) ξ :=
    (differentiableAt_const x).prodMk differentiableAt_id
  exact ⟨DifferentiableAt.comp (g := aChart) x hD hBase,
    DifferentiableAt.comp (g := aChart) ξ hD hMomentum⟩

private theorem fderiv_sub_div_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : V → ℝ} {x : V} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : V) :
    fderiv ℝ (fun y => (f y - g y) / 2) x v = (fderiv ℝ f x v - fderiv ℝ g x v) / 2 := by
  have he : (fun y => (f y - g y) / 2) = (2 : ℝ)⁻¹ • (f - g) := by
    funext y
    simp [div_eq_mul_inv, mul_comm]
  rw [he, fderiv_const_smul_of_field]
  change (2 : ℝ)⁻¹ * (fderiv ℝ (f - g) x) v = _
  rw [fderiv_sub hf hg]
  simp [div_eq_mul_inv, mul_comm]

private theorem canonicalBracket_sub_div_two (P a b : E → Covector → ℝ) (x : E) (ξ : Covector)
    (ha : DifferentiableAt ℝ (fun y => a y ξ) x ∧ DifferentiableAt ℝ (a x) ξ)
    (hb : DifferentiableAt ℝ (fun y => b y ξ) x ∧ DifferentiableAt ℝ (b x) ξ) :
    canonicalBracket P (fun y η => (a y η - b y η) / 2) x ξ =
      (canonicalBracket P a x ξ - canonicalBracket P b x ξ) / 2 := by
  unfold canonicalBracket
  conv_rhs => rw [div_eq_mul_inv, ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [basePartial, momentumPartial, fderiv_sub_div_two ha.1 hb.1, fderiv_sub_div_two ha.2 hb.2]
  ring

private theorem unit_cotangentCoords_ne_zero (r : Metric (M := M)) (c : M) (p : Cosphere r)
    (hp : p.val.proj ∈ (chartAt E c).source) : cotangentCoords c p.val ≠ 0 := by
  intro hz
  have h := dualEnergy_chart r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm c p.val hp
  have hOne : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p.val = 1 := p.property
  rw [hz, hOne] at h
  simp [symbolNorm] at h

/-- The selected actual chart derivative of the odd part is the average of
the derivative of the test at a point and its antipode. -/
theorem hamiltonDerivativeOnCosphere_oddPart (r : Metric (M := M))
    (B : Field (M := M)) (hn : IsNondegenerate B) (a : CotangentBundle M → ℝ)
    (ha : IsDegreeOneTransportTest a) (p : Cosphere r) :
    basePointHamiltonDerivative B hn (oddTransportPart a) p.val =
      (basePointHamiltonDerivative B hn a p.val + basePointHamiltonDerivative B hn a (antipode r p).val) / 2 := by
  let c := p.val.proj
  let x := chartAt E c p.val.proj
  let ξ := cotangentCoords c p.val
  have hc : p.val.proj ∈ (chartAt E c).source := mem_chart_source E _
  have hx : x ∈ (chartAt E c).target := (chartAt E c).mapsTo hc
  have hξ : ξ ≠ 0 := unit_cotangentCoords_ne_zero r c p hc
  let aR := a ∘ cotangentScale (-1)
  have hLocalA := differentiableAt_chartSlices c a ha.1 x hx ξ hξ
  have hLocalR := differentiableAt_chartSlices c aR ha.reflect.1 x hx ξ hξ
  calc
    _ = (basePointHamiltonDerivative B hn a p.val - basePointHamiltonDerivative B hn aR p.val) / 2 := by
      change canonicalBracket (chartHamiltonian c B hn)
        (fun y η => (a (cotangentChartInverse c (y, η)) - aR (cotangentChartInverse c (y, η))) / 2) x ξ = _
      exact canonicalBracket_sub_div_two _ _ _ x ξ hLocalA hLocalR
    _ = _ := by
      have h := hamiltonDerivativeOnCosphere_reflect r B hn a p
      change basePointHamiltonDerivative B hn aR p.val = _ at h
      rw [h, sub_neg_eq_add]

/-- On one reflection-invariant measure, the Hamilton derivative of an
integrable real test and that of its odd part have the same integral. -/
theorem integral_hamiltonDerivative_oddPart (r : Metric (M := M))
    (B : Field (M := M)) (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hEven : μ.map (antipode r) = μ) (a : CotangentBundle M → ℝ) (ha : IsDegreeOneTransportTest a)
    (hI : Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ) :
    (∫ p : Cosphere r, basePointHamiltonDerivative B hn (oddTransportPart a) p.val ∂μ) =
      ∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ := by
  let F (p : Cosphere r) := basePointHamiltonDerivative B hn a p.val
  have hEmb := measurableEmbedding_antipode r
  have hRI : Integrable (F ∘ antipode r) μ := hEmb.integrable_map_iff.mp (hEven.symm ▸ hI)
  have hR := hEmb.integral_map (μ := μ) F
  rw [hEven] at hR
  change (∫ p, F p ∂μ) = (∫ p, (F ∘ antipode r) p ∂μ) at hR
  calc
    _ = ∫ p : Cosphere r, (F p + (F ∘ antipode r) p) / 2 ∂μ := by
      exact integral_congr_ae (ae_of_all _ (hamiltonDerivativeOnCosphere_oddPart r B hn a ha))
    _ = (∫ p, F p ∂μ) := by
      rw [integral_div, integral_add hI hRI, ← hR]
      ring

/-- The reduction for all real degree-one tests on the very same measure.
The integrability input makes the transport integrals genuine Bochner integrals. -/
theorem transport_of_oddTests_of_antipodalMeasure (r : Metric (M := M))
    (B : Field (M := M)) (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hEven : μ.map (antipode r) = μ)
    (hOdd : ∀ b, IsDegreeOneTransportTest b → IsAntipodallyOdd b →
      ∫ p : Cosphere r, basePointHamiltonDerivative B hn b p.val ∂μ = 0)
    (hIntegrable : ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) = 0 := by
  intro a ha
  have hI := hIntegrable a ha
  refine ⟨hI, ?_⟩
  rw [← integral_hamiltonDerivative_oddPart r B hn μ hEven a ha hI]
  exact hOdd _ ha.oddPart (oddTransportPart_odd a)

end Burnett.C04
