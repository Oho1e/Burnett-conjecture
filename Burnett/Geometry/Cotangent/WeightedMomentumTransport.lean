import Burnett.Geometry.Cotangent.WeightedMomentumMeasure

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.ActualTestLift

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.RadialHamilton Burnett.Geometry.CotangentHamiltonNaturality
open Burnett.Geometry.CotangentSymplecticTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem cotangentChart_mem_puncturedPhaseTarget (c : M) {p : CotangentBundle M}
    (hc : p ∈ cotangentSource c) (hp : p ∈ puncturedCotangent) :
    cotangentChart c p ∈ puncturedPhaseTarget c := by
  refine ⟨cotangentChart_mapsTo c hc, ?_⟩
  intro hq
  have hq' : cotangentCoords c p = 0 := hq
  have hz : cotangentScale (0 : ℝ) p ∈ cotangentSource c := hc
  have he : cotangentChart c (cotangentScale (0 : ℝ) p) = cotangentChart c p := by
    rw [cotangentChart_scale]
    simp [phaseScale_apply, cotangentChart, hq']
  have hh := congrArg (cotangentChartInverse c) he
  rw [cotangentChart_left_inv c hz, cotangentChart_left_inv c hc] at hh
  have hbad : cotangentScale (0 : ℝ) p ∈ puncturedCotangent := by rwa [hh]
  change (0 : ℝ) • p.2 ≠ 0 at hbad
  exact hbad (zero_smul ℝ _)

theorem isOpen_puncturedCotangent : IsOpen (puncturedCotangent (M := M)) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let c := p.1
  let W := cotangentSource c ∩ cotangentChart c ⁻¹' puncturedPhaseTarget c
  have hc : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  have hW : IsOpen W :=
    (contMDiffOn_cotangentChart c).continuousOn.isOpen_inter_preimage
      (isOpen_cotangentSource c) (isOpen_puncturedPhaseTarget c)
  apply Filter.mem_of_superset (hW.mem_nhds ⟨hc, cotangentChart_mem_puncturedPhaseTarget c hc hp⟩)
  intro x hx
  have hx' := cotangentChartInverse_mem_punctured hx.2
  rwa [cotangentChart_left_inv c hx.1] at hx'

theorem contDiffOn_cotangent_test_chart (c : M) (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) :
    ContDiffOn ℝ ∞ (a ∘ cotangentChartInverse c) (puncturedPhaseTarget c) := by
  have hh : ContMDiffOn CoordinatePhaseModel 𝓘(ℝ) ∞
      (a ∘ cotangentChartInverse c) (puncturedPhaseTarget c) :=
    ha.comp ((contMDiffOn_cotangentChartInverse c).mono (fun _ hp => hp.1))
      (fun _ hp => cotangentChartInverse_mem_punctured hp)
  simp only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
  exact hh.contDiffOn

def chartHamiltonDerivative (g : ManifoldBilinear.Field (M := M)) (c : M)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  fderiv ℝ (a ∘ cotangentChartInverse c) (cotangentChart c p)
    (hamiltonVector (chartInverse g c) (cotangentChart c p))

/-- The actual chart derivative of a scalar test is invariant on the overlap. -/
theorem chartHamiltonDerivative_eq_on_overlap
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (c d : M) {p : CotangentBundle M} (hc : p ∈ cotangentSource c) (hd : p ∈ cotangentSource d)
    (hp : p ∈ puncturedCotangent) :
    chartHamiltonDerivative g c a p = chartHamiltonDerivative g d a p := by
  let q := cotangentChart c p
  let Φ := cotangentTransition c d
  have hq := chart_mem_transitionSource c d p hc hd
  have hΦ : DifferentiableAt ℝ Φ q := ((cotangentTransition_contDiffOn c d).contDiffAt
    ((transitionSource_isOpen c d).mem_nhds hq)).differentiableAt (by simp)
  have hΦq : Φ q = cotangentChart d p := cotangentTransition_chart c d p hc
  have hA : DifferentiableAt ℝ (a ∘ cotangentChartInverse d) (Φ q) := by
    rw [hΦq]
    have h := (contDiffOn_cotangent_test_chart d a ha).contDiffAt
      ((isOpen_puncturedPhaseTarget d).mem_nhds (cotangentChart_mem_puncturedPhaseTarget d hd hp))
    exact h.differentiableAt (by simp)
  have he : ((a ∘ cotangentChartInverse d) ∘ Φ) =ᶠ[𝓝 q] (a ∘ cotangentChartInverse c) := by
    filter_upwards [(transitionSource_isOpen c d).mem_nhds hq] with z hz
    have hs : cotangentChartInverse c z ∈ cotangentSource d := hz.2
    simp only [Function.comp_apply, Φ, cotangentTransition, cotangentChart_left_inv d hs]
  have hchain := (hA.hasFDerivAt.comp q hΦ.hasFDerivAt).fderiv
  rw [he.fderiv_eq, hΦq] at hchain
  have hh := congrArg (fun D : Phase →L[ℝ] ℝ => D (hamiltonVector (chartInverse g c) q)) hchain
  change fderiv ℝ (a ∘ cotangentChartInverse c) q (hamiltonVector (chartInverse g c) q) =
    fderiv ℝ (a ∘ cotangentChartInverse d) (cotangentChart d p)
      (fderiv ℝ (cotangentTransition c d) q (hamiltonVector (chartInverse g c) q)) at hh
  rw [actual_hamiltonVector_chart_compatible g hg hgn hgs c d p hc hd] at hh
  exact hh

def actualHamiltonDerivative (g : ManifoldBilinear.Field (M := M)) (a : CotangentBundle M → ℝ)
    (p : CotangentBundle M) : ℝ :=
  chartHamiltonDerivative g p.1 a p

theorem actualHamiltonDerivative_in_chart
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (c : M) {p : CotangentBundle M} (hc : p ∈ cotangentSource c) (hp : p ∈ puncturedCotangent) :
    actualHamiltonDerivative g a p = chartHamiltonDerivative g c a p :=
  chartHamiltonDerivative_eq_on_overlap g hg hgn hgs a ha p.1 c
    (mem_chart_source CoordinateSpace p.1) hc hp

theorem continuousOn_actualHamiltonDerivative
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) :
    ContinuousOn (actualHamiltonDerivative g a) puncturedCotangent := by
  intro p hp
  let c := p.1
  have hc : p ∈ cotangentSource c := mem_chart_source CoordinateSpace p.1
  let W := cotangentSource c ∩ puncturedCotangent
  have hW : IsOpen W := (isOpen_cotangentSource c).inter isOpen_puncturedCotangent
  have hpW : p ∈ W := ⟨hc, hp⟩
  have hcA := contDiffOn_cotangent_test_chart c a ha
  have hf := hcA.continuousOn_fderiv_of_isOpen (isOpen_puncturedPhaseTarget c) (by simp)
  have hH := (contDiffOn_hamiltonVector_chartInverse g hg hgn c).continuousOn
  let F := fun q => fderiv ℝ (a ∘ cotangentChartInverse c) q (hamiltonVector (chartInverse g c) q)
  have hF : ContinuousOn F (puncturedPhaseTarget c) := hf.clm_apply (hH.mono (fun _ q => q.1))
  have hchart : ContinuousOn (cotangentChart c) W :=
    (contMDiffOn_cotangentChart c).continuousOn.mono (fun _ q => q.1)
  have hcomp : ContinuousOn (F ∘ cotangentChart c) W :=
    hF.comp hchart (fun _ hq => cotangentChart_mem_puncturedPhaseTarget c hq.1 hq.2)
  have hA : ContinuousOn (actualHamiltonDerivative g a) W := hcomp.congr (fun _ hq =>
    actualHamiltonDerivative_in_chart g hg hgn hgs a ha c hq.1 hq.2)
  exact ((hA.continuousAt (hW.mem_nhds hpW))).continuousWithinAt

end Burnett.Geometry.ActualTestLift

namespace Burnett.Geometry.ActualTestLift

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def actualSection (s : CotangentBundle M → ℝ) (p : CotangentBundle M) : CotangentBundle M :=
  cotangentScale (s p) p

theorem actualSection_mem_punctured (s : CotangentBundle M → ℝ) {p : CotangentBundle M}
    (hp : p ∈ puncturedCotangent) (hs : s p ≠ 0) : actualSection s p ∈ puncturedCotangent := by
  change s p • p.2 ≠ 0
  exact smul_ne_zero hs hp

theorem coordinateSection_cotangentChart (c : M) (s : CotangentBundle M → ℝ)
    {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    coordinateSection (s ∘ cotangentChartInverse c) (cotangentChart c p) =
      cotangentChart c (actualSection s p) := by
  unfold coordinateSection phaseRay actualSection
  rw [Function.comp_apply, cotangentChart_left_inv c hp, cotangentChart_scale]

theorem weightedTrace_chart (c : M) (b s : CotangentBundle M → ℝ)
    {q : Phase} (hq : q ∈ phaseTarget c) :
    intrinsicWeightedTrace b s (cotangentChartInverse c q) =
      (b ∘ cotangentChartInverse c) (coordinateSection (s ∘ cotangentChartInverse c) q) /
        (s ∘ cotangentChartInverse c) q := by
  let p := cotangentChartInverse c q
  have hp : p ∈ cotangentSource c := cotangentChartInverse_mapsTo c hq
  have hL : actualSection s p ∈ cotangentSource c := hp
  have h := coordinateSection_cotangentChart c s hp
  rw [cotangentChart_right_inv c hq] at h
  rw [h, Function.comp_apply, cotangentChart_left_inv c hL]
  rfl

theorem degreeOne_chart (c : M) (r : Metric (M := M)) (f : CotangentBundle M → ℝ)
    {q : Phase} (hq : q ∈ phaseTarget c) :
    degreeOneRadialExtension r f (cotangentChartInverse c q) =
      coordinateDegreeOne r c (f ∘ cotangentChartInverse c) q := by
  have h := coordinateDegreeOne_cotangentChart r c f (cotangentChartInverse_mapsTo c hq)
  rw [cotangentChart_right_inv c hq] at h
  exact h.symm

def scaleInvariantInChart (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (c : M) (s : CotangentBundle M → ℝ) (p : CotangentBundle M) : Prop :=
  let q := cotangentChart c p
  let G := chartInverse g c
  fderiv ℝ (s ∘ cotangentChartInverse c) q (angularVector G r c q) =
    radialCoefficient G r c q * s p

/-- At the same true unit-null point, a valid angular extension yields the weighted section formula. -/
theorem actual_hamilton_test_section_weight
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c : M)
    (b s f : CotangentBundle M → ℝ)
    (hb : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent)
    (hs : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent)
    (hf : ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ f)
    (htrace : EqOn f (intrinsicWeightedTrace b s) (cotangentUnitNull r g hgn))
    {p : CotangentBundle M} (hc : p ∈ cotangentSource c) (hp : p ∈ cotangentUnitNull r g hgn)
    (hspos : 0 < s p) (hI : scaleInvariantInChart r g c s p) :
    actualHamiltonDerivative g b (actualSection s p) =
      (s p)^2 * actualHamiltonDerivative g (degreeOneRadialExtension r f) p := by
  let q := cotangentChart c p
  let B := b ∘ cotangentChartInverse c
  let S := s ∘ cotangentChartInverse c
  let F := fun z => B (coordinateSection S z) / S z
  let G := chartInverse g c
  have hval : S q = s p := congrArg s (cotangentChart_left_inv c hc)
  have hp0 : p ∈ puncturedCotangent := cotangentUnitNull_covector_ne_zero r g hgn hp
  have hq := cotangentChart_mem_puncturedPhaseTarget c hc hp0
  have hcL : actualSection s p ∈ cotangentSource c := hc
  have hLp := actualSection_mem_punctured s hp0 hspos.ne'
  have hcoordL := coordinateSection_cotangentChart c s hc
  have hqL : coordinateSection S q ∈ puncturedPhaseTarget c := by
    change coordinateSection (s ∘ cotangentChartInverse c) (cotangentChart c p) ∈ _
    rw [hcoordL]
    exact cotangentChart_mem_puncturedPhaseTarget c hcL hLp
  have hu : coordinateNorm r c q = 1 := by
    change coordinateNorm r c (cotangentChart c p) = _
    rw [coordinateNorm_cotangentChart r c hc, cotangentNorm, hp.1, Real.sqrt_one]
  have hnull : coordinateP G q = 0 := by
    change coordinateP (chartInverse g c) (cotangentChart c p) = _
    rw [coordinateP_cotangentChart g hgn hgs c hc, hp.2, zero_div]
  have hS : DifferentiableAt ℝ S q := ((contDiffOn_cotangent_test_chart c s hs).contDiffAt
    ((isOpen_puncturedPhaseTarget c).mem_nhds hq)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B (coordinateSection S q) :=
    ((contDiffOn_cotangent_test_chart c b hb).contDiffAt
      ((isOpen_puncturedPhaseTarget c).mem_nhds hqL)).differentiableAt (by simp)
  have hSpos : 0 < S q := by rwa [hval]
  have hI' : fderiv ℝ S q (angularVector G r c q) = radialCoefficient G r c q * S q := by
    rw [hval]
    exact hI
  have hL : DifferentiableAt ℝ (coordinateSection S) q := by
    let L := fun z : Phase => (S z, z)
    have hL : DifferentiableAt ℝ L q := hS.prodMk differentiableAt_id
    have hh : DifferentiableAt ℝ phaseRay (L q) := contDiff_phaseRay.differentiable (by simp) _
    exact hh.comp q hL
  have hF : DifferentiableAt ℝ F q := by
    have hh := (hB.comp q hL).mul (hS.inv hSpos.ne')
    simpa only [F, Function.comp_apply, div_eq_mul_inv, Pi.inv_apply, Pi.mul_apply] using hh
  have hA := degreeOneRadialExtension_smooth r f hf
  have hAchart := ((contDiffOn_cotangent_test_chart c _ hA).contDiffAt
    ((isOpen_puncturedPhaseTarget c).mem_nhds hq)).differentiableAt (by simp)
  have he : (degreeOneRadialExtension r (intrinsicWeightedTrace b s) ∘ cotangentChartInverse c)
      =ᶠ[𝓝 q] coordinateDegreeOne r c F := by
    filter_upwards [(isOpen_puncturedPhaseTarget c).mem_nhds hq] with z hz
    change degreeOneRadialExtension r (intrinsicWeightedTrace b s) (cotangentChartInverse c z) = _
    rw [degreeOne_chart c r _ hz.1]
    change coordinateNorm r c z * intrinsicWeightedTrace b s (cotangentChartInverse c (coordinateNormalize r c z)) =
      coordinateNorm r c z * F (coordinateNormalize r c z)
    rw [weightedTrace_chart c b s (coordinateNormalize_mem_puncturedPhaseTarget r c hz).1]
  have hFn : DifferentiableAt ℝ F (coordinateNormalize r c q) := by
    rwa [coordinateNormalize_of_norm_one r c hu]
  have hNc := (contDiffAt_coordinateNorm r c hq).differentiableAt (by simp)
  have hNr := (contDiffAt_coordinateNormalize r c hq).differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (coordinateDegreeOne r c F) q := hNc.mul (hFn.comp q hNr)
  have hAref := hD.congr_of_eventuallyEq he
  have hmatch := fderiv_apply_actual_hamiltonVector_eq_of_same_unitNull_trace g hg hgn hgs r c
    hq hnull f (intrinsicWeightedTrace b s) hAchart hAref htrace
  dsimp only at hmatch
  rw [he.fderiv_eq] at hmatch
  have hweight := coordinateDegreeOne_transport_weight G r c S B hq hu hS hSpos hI' hB
  dsimp only at hweight
  rw [actualHamiltonDerivative_in_chart g hg hgn hgs b hb c hcL hLp,
    actualHamiltonDerivative_in_chart g hg hgn hgs _ hA c hc hp0]
  change fderiv ℝ B (cotangentChart c (actualSection s p))
    (hamiltonVector G (cotangentChart c (actualSection s p))) =
      (s p)^2 * fderiv ℝ (degreeOneRadialExtension r f ∘ cotangentChartInverse c) q (hamiltonVector G q)
  rw [← hcoordL, hmatch, ← hval]
  exact hweight

end Burnett.Geometry.ActualTestLift

namespace Burnett.Geometry.ActualTestLift

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.FullMomentumLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

local instance puncturedMeasurable : MeasurableSpace (puncturedCotangent (M := M)) := borel _
local instance puncturedBorel : BorelSpace (puncturedCotangent (M := M)) := ⟨rfl⟩

local instance unitNullMeasurable (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) : MeasurableSpace (cotangentUnitNull r g hgn) := borel _
local instance unitNullBorel (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) : BorelSpace (cotangentUnitNull r g hgn) := ⟨rfl⟩

def actualUnitSection (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : CotangentBundle M → ℝ)
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p) :
    cotangentUnitNull r g hgn → puncturedCotangent (M := M) :=
  fun p => ⟨actualSection s p.val,
    actualSection_mem_punctured s (cotangentUnitNull_covector_ne_zero r g hgn p.property)
      (hpos p.val p.property).ne'⟩

theorem continuous_actualUnitSection (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : CotangentBundle M → ℝ)
    (hs : ContinuousOn s (cotangentUnitNull r g hgn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p) :
    Continuous (actualUnitSection r g hgn s hpos) := by
  have hL : Continuous (fun p : cotangentUnitNull r g hgn => actualSection s p.val) :=
    continuous_cotangentScale.comp ((continuousOn_iff_continuous_restrict.mp hs).prodMk
      continuous_subtype_val)
  exact hL.subtype_mk _

def actualWeightedLift (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (s : CotangentBundle M → ℝ)
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p)
    (μ : Measure (cotangentUnitNull r g hgn)) : Measure (puncturedCotangent (M := M)) :=
  weightedLift μ (actualUnitSection r g hgn s hpos) (fun p => s p.val)

def HasActualUnitTransport (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (μ : Measure (cotangentUnitNull r g hgn)) : Prop :=
  ∀ a : CotangentBundle M → ℝ,
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
    (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
    (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
    (∫ p : cotangentUnitNull r g hgn, actualHamiltonDerivative g a p.val ∂μ) = 0

theorem actualHamiltonDerivative_zero_off_closed_base
    (g : ManifoldBilinear.Field (M := M)) (a : CotangentBundle M → ℝ)
    {K : Set M} (hK : IsClosed K) (hA : tsupport a ⊆ (fun p => p.1) ⁻¹' K)
    {p : CotangentBundle M} (hp : p.1 ∉ K) :
    actualHamiltonDerivative g a p = 0 := by
  let c := p.1
  let q := cotangentChart c p
  have hc : p ∈ cotangentSource c := mem_chart_source CoordinateSpace p.1
  have hq : q ∈ phaseTarget c := cotangentChart_mapsTo c hc
  have hC : ContinuousAt (cotangentChartInverse c) q :=
    (contMDiffOn_cotangentChartInverse c).continuousOn.continuousAt ((isOpen_phaseTarget c).mem_nhds hq)
  have hbase : ContinuousAt (fun z => (cotangentChartInverse c z).1) q :=
    continuous_cotangent_projection.continuousAt.comp hC
  have hinv : (cotangentChartInverse c q).1 ∈ Kᶜ := by
    rw [cotangentChart_left_inv c hc]
    exact hp
  have hnear : ∀ᶠ z in 𝓝 q, (cotangentChartInverse c z).1 ∈ Kᶜ :=
    hbase (hK.isOpen_compl.mem_nhds hinv)
  have hz : (a ∘ cotangentChartInverse c) =ᶠ[𝓝 q] (fun _ => (0 : ℝ)) := hnear.mono fun z hz => by
    change a (cotangentChartInverse c z) = 0
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hz (hA h)
  have hd : fderiv ℝ (fun _ : Phase => (0 : ℝ)) q = 0 := (hasFDerivAt_const (0 : ℝ) q).fderiv
  change fderiv ℝ (a ∘ cotangentChartInverse c) q (hamiltonVector (chartInverse g c) q) = 0
  rw [hz.fderiv_eq, hd, ContinuousLinearMap.zero_apply]

theorem integrable_unit_actualHamiltonDerivative [T2Space M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g)
    (μ : Measure (cotangentUnitNull r g hgn)) [IsLocallyFiniteMeasure μ]
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    {K : Set M} (hK : IsCompact K) (hA : tsupport a ⊆ (fun p => p.1) ⁻¹' K) :
    Integrable (fun p : cotangentUnitNull r g hgn => actualHamiltonDerivative g a p.val) μ := by
  letI := cotangentBundle_t2Space (M := M)
  let J := fun p : cotangentUnitNull r g hgn => actualHamiltonDerivative g a p.val
  let C := {p : cotangentUnitNull r g hgn | p.val.1 ∈ K}
  have hC : IsCompact C := isCompact_cotangentUnitNullSubtype_preimage r g hg hgn hgs hK
  have hcJ : Continuous J := (continuousOn_actualHamiltonDerivative g hg hgn hgs a ha).comp_continuous
    continuous_subtype_val (fun p => cotangentUnitNull_covector_ne_zero r g hgn p.property)
  have hcompJ : HasCompactSupport J := hC.of_isClosed_subset (isClosed_tsupport J) <|
    closure_minimal
      (fun p hp => by
        by_contra hc
        exact hp (actualHamiltonDerivative_zero_off_closed_base g a hK.isClosed hA hc))
      hC.isClosed
  exact hcJ.integrable_of_hasCompactSupport hcompJ

/-- The actual compact test on the punctured bundle is transported by the actual weighted measure. -/
theorem actual_full_transport_of_invariant_scale [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g)
    (μ : Measure (cotangentUnitNull r g hgn)) [IsLocallyFiniteMeasure μ]
    (s : CotangentBundle M → ℝ)
    (hs : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent)
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p)
    (hI : ∀ p ∈ cotangentUnitNull r g hgn, scaleInvariantInChart r g p.1 s p)
    (ht : HasActualUnitTransport r g hgn μ)
    (b : CotangentBundle M → ℝ)
    (hb : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent)
    (hcompact : HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.val)) :
    Integrable (fun p : puncturedCotangent (M := M) => actualHamiltonDerivative g b p.val)
      (actualWeightedLift r g hgn s hpos μ) ∧
      (∫ p : puncturedCotangent (M := M), actualHamiltonDerivative g b p.val
        ∂actualWeightedLift r g hgn s hpos μ) = 0 := by
  let U := cotangentUnitNull r g hgn
  let F := fun p : puncturedCotangent (M := M) => actualHamiltonDerivative g b p.val
  let L := actualUnitSection r g hgn s hpos
  let σ := fun p : U => s p.val
  have hS : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s U :=
    hs.mono (fun _ hp => cotangentUnitNull_covector_ne_zero r g hgn hp)
  obtain ⟨K, hK, f, hf, htrace, hF⟩ :=
    actual_weightedTrace_angular_extension r g hg hgn hgs b s hb hcompact hS hpos
  let a := degreeOneRadialExtension r f
  have ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent :=
    degreeOneRadialExtension_smooth r f hf
  have hKbase := degreeOneRadialExtension_tsupport r f hK.isClosed hF
  let J := fun p : U => actualHamiltonDerivative g a p.val
  have hweight (p : U) : F (L p) = σ p ^ 2 * J p :=
    actual_hamilton_test_section_weight r g hg hgn hgs p.val.1 b s f hb hs hf htrace
      (mem_chart_source CoordinateSpace p.val.1) p.property (hpos _ p.property) (hI _ p.property)
  have hLm : Measurable L := (continuous_actualUnitSection r g hgn s hS.continuousOn hpos).measurable
  have hSm : Measurable σ := (continuousOn_iff_continuous_restrict.mp hS.continuousOn).measurable
  have hFm : Measurable F :=
    (continuousOn_iff_continuous_restrict.mp (continuousOn_actualHamiltonDerivative g hg hgn hgs b hb)).measurable
  have hh := weightedLift_pairing_cancel μ L σ hLm hSm
    (fun p => (hpos _ p.property).ne') F hFm J hweight
  have hJi := integrable_unit_actualHamiltonDerivative r g hg hgn hgs μ a ha hK hKbase
  have hzero : (∫ p : U, J p ∂μ) = 0 :=
    ht a ha (fun _ hp t ht => degreeOneRadialExtension_scale r f hp ht) ⟨K, hK, hKbase⟩
  exact ⟨hh.1.mpr hJi, hh.2.trans hzero⟩

end Burnett.Geometry.ActualTestLift

namespace Burnett.Geometry.ActualTestLift

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem cotangentChartInverse_phaseScale (c : M) {q : Phase}
    (hq : q ∈ phaseTarget c) (t : ℝ) :
    cotangentChartInverse c (phaseScale t q) = cotangentScale t (cotangentChartInverse c q) := by
  let p := cotangentChartInverse c q
  have hp : p ∈ cotangentSource c := cotangentChartInverse_mapsTo c hq
  have htp : cotangentScale t p ∈ cotangentSource c := hp
  have h := cotangentChart_scale c t p
  rw [cotangentChart_right_inv c hq] at h
  rw [← h, cotangentChart_left_inv c htp]

/-- The reciprocal of an actual homogeneous first integral satisfies the true scale equation. -/
theorem scaleInvariantInChart_of_degreeOneEnergy
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (c : M)
    (E : CotangentBundle M → ℝ)
    (hE : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ E puncturedCotangent)
    (hhom : ∀ w ∈ puncturedCotangent, ∀ t > (0 : ℝ), E (cotangentScale t w) = t * E w)
    {p : CotangentBundle M} (hc : p ∈ cotangentSource c) (hp : p ∈ cotangentUnitNull r g hgn)
    (hpos : 0 < E p) (hH : chartHamiltonDerivative g c E p = 0) :
    scaleInvariantInChart r g c (fun w => (E w)⁻¹) p := by
  let q := cotangentChart c p
  let C := E ∘ cotangentChartInverse c
  let G := chartInverse g c
  have hpp : p ∈ puncturedCotangent := cotangentUnitNull_covector_ne_zero r g hgn hp
  have hq := cotangentChart_mem_puncturedPhaseTarget c hc hpp
  have hu : coordinateNorm r c q = 1 := by
    change coordinateNorm r c (cotangentChart c p) = _
    rw [coordinateNorm_cotangentChart r c hc, cotangentNorm, hp.1, Real.sqrt_one]
  have hC := ((contDiffOn_cotangent_test_chart c E hE).contDiffAt
    ((isOpen_puncturedPhaseTarget c).mem_nhds hq)).differentiableAt (by simp)
  have hEc : C q = E p := congrArg E (cotangentChart_left_inv c hc)
  have hChom : ∀ w ∈ puncturedPhaseTarget c, ∀ t > (0 : ℝ), C (phaseScale t w) = t * C w := by
    intro w hw t ht
    simpa only [C, Function.comp_apply, cotangentChartInverse_phaseScale c hw.1 t] using
      hhom (cotangentChartInverse c w) (cotangentChartInverse_mem_punctured hw) t ht
  have hposC : 0 < C q := hEc.symm ▸ hpos
  have h := inverse_energy_derivative_eq_radialCoefficient_mul G r c C hChom hq hu hC hposC hH
  rw [hEc] at h
  exact h

end Burnett.Geometry.ActualTestLift

namespace Burnett.Geometry.ActualTestLift

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Positive angular energy data admits a positive one-homogeneous smooth extension. -/
theorem exists_positive_degreeOne_energy_extension [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (E : CotangentBundle M → ℝ)
    (hE : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ E (cotangentUnitNull r g hgn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < E p) :
    ∃ F : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ F puncturedCotangent ∧
      (∀ p ∈ puncturedCotangent, 0 < F p) ∧
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), F (cotangentScale t p) = t * F p) ∧
      EqOn F E (cotangentUnitNull r g hgn) := by
  let U := cotangentUnitNull r g hgn
  let ℓ := fun p => Real.log (E p)
  have hℓ : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ ℓ U := by
    intro p hp
    have hlog := (Real.contDiffAt_log.mpr (hpos p hp).ne' :
      ContDiffAt ℝ ∞ Real.log (E p)).contMDiffAt
    exact hlog.comp_contMDiffWithinAt p (hE p hp)
  letI := finiteDimensional_cotangentModel
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_sigmaCompact (M := M)
  obtain ⟨e, he, heq, _⟩ :=
    Burnett.Geometry.AngularExtension.extend_closed_with_base_support CotangentModelWithCorners
      (isClosed_cotangentUnitNull r g hg hgn hgs) ℓ (fun p : CotangentBundle M => p.1)
      continuous_cotangent_projection (isClosed_univ : IsClosed (univ : Set M))
      (fun p hp => local_actual_cotangent_extension r g hg hgn hgs ℓ hℓ
        (K := univ) (fun _ _ h => (h (mem_univ _)).elim) p hp)
  let f := Real.exp ∘ e
  have hf : ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ f :=
    Real.contDiff_exp.contMDiff.comp he
  refine ⟨degreeOneRadialExtension r f, degreeOneRadialExtension_smooth r f hf, ?_,
    fun p hp t ht => degreeOneRadialExtension_scale r f hp ht, ?_⟩
  · intro p hp
    exact mul_pos (cotangentNorm_pos r hp) (Real.exp_pos _)
  · intro p hp
    rw [degreeOneRadialExtension_of_auxiliary_one r f p hp.1]
    change Real.exp (e p) = E p
    rw [heq hp]
    exact Real.exp_log (hpos p hp)

theorem eq_of_positive_homogeneous_of_unitNull_trace
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (E F : CotangentBundle M → ℝ)
    (hEhom : ∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 →
      ∀ t > (0 : ℝ), E (cotangentScale t p) = t * E p)
    (hFhom : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), F (cotangentScale t p) = t * F p)
    (hEF : EqOn F E (cotangentUnitNull r g hgn))
    {p : CotangentBundle M} (hpp : p ∈ puncturedCotangent) (hn : dualEnergy g hgn p = 0) :
    F p = E p := by
  let N := cotangentNorm r p
  let u := cotangentNormalize r p
  have hN : 0 < N := cotangentNorm_pos r hpp
  have hu : u ∈ cotangentUnitNull r g hgn := cotangentNormalize_mem_unitNull r g hgn hpp hn
  have huu : u ∈ puncturedCotangent := cotangentUnitNull_covector_ne_zero r g hgn hu
  have hrec : cotangentScale N u = p := by
    change cotangentScale N (cotangentNormalize r p) = p
    rw [cotangentNormalize, cotangentScale_mul]
    change cotangentScale (N * N⁻¹) p = p
    rw [mul_inv_cancel₀ hN.ne', cotangentScale_one]
  calc
    F p = F (cotangentScale N u) := congrArg F hrec.symm
    _ = N * F u := hFhom u huu N hN
    _ = N * E u := by rw [hEF hu]
    _ = E (cotangentScale N u) := (hEhom u huu hu.2 N hN).symm
    _ = E p := congrArg E hrec

/-- A positive homogeneous extension retains every given null first integral at the unit points. -/
theorem actualHamiltonDerivative_of_eq_null_trace_at_unit
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (E F : CotangentBundle M → ℝ)
    (hF : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ F puncturedCotangent)
    (hEq : ∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 → F p = E p)
    {p : CotangentBundle M} (hp : p ∈ cotangentUnitNull r g hgn)
    (hE : ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p) :
    actualHamiltonDerivative g F p = actualHamiltonDerivative g E p := by
  let c := p.1
  let q := cotangentChart c p
  have hc : p ∈ cotangentSource c := mem_chart_source CoordinateSpace p.1
  have hu : p ∈ puncturedCotangent := cotangentUnitNull_covector_ne_zero r g hgn hp
  have hq := cotangentChart_mem_puncturedPhaseTarget c hc hu
  have hzero : coordinateP (chartInverse g c) q = 0 := by
    change coordinateP (chartInverse g c) (cotangentChart c p) = _
    rw [coordinateP_cotangentChart g hgn hgs c hc, hp.2, zero_div]
  have hA := ((contDiffOn_cotangent_test_chart c F hF).contDiffAt
    ((isOpen_puncturedPhaseTarget c).mem_nhds hq)).differentiableAt (by simp)
  have hInv : ContMDiffAt CoordinatePhaseModel CotangentModelWithCorners ∞
      (cotangentChartInverse c) q := (contMDiffOn_cotangentChartInverse c).contMDiffAt
        ((isOpen_phaseTarget c).mem_nhds hq.1)
  have hC : ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E (cotangentChartInverse c q) := by
    change ContMDiffAt _ _ _ E (cotangentChartInverse c (cotangentChart c p))
    rwa [cotangentChart_left_inv c hc]
  have hB := hC.comp q hInv
  simp only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hB
  exact fderiv_apply_actual_hamiltonVector_eq_of_same_null_trace g hg hgn hgs c
    hq hzero F E hA (hB.contDiffAt.differentiableAt (by simp)) (fun p _ => hEq p)
/-- Extend a genuine null first integral to a smooth positive homogeneous representative. -/
theorem exists_positive_degreeOne_firstIntegral_extension [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (E : CotangentBundle M → ℝ)
    (hE : ∀ p ∈ cotangentUnitNull r g hgn, ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p)
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < E p)
    (hhom : ∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 →
      ∀ t > (0 : ℝ), E (cotangentScale t p) = t * E p)
    (hH : ∀ p ∈ cotangentUnitNull r g hgn, actualHamiltonDerivative g E p = 0) :
    ∃ F : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ F puncturedCotangent ∧
      (∀ p ∈ puncturedCotangent, 0 < F p) ∧
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), F (cotangentScale t p) = t * F p) ∧
      (∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 → F p = E p) ∧
      (∀ p ∈ cotangentUnitNull r g hgn, actualHamiltonDerivative g F p = 0) := by
  obtain ⟨F, hF, hFpos, hFhom, he⟩ :=
    exists_positive_degreeOne_energy_extension r g hg hgn hgs E
      (fun p hp => (hE p hp).contMDiffWithinAt) hpos
  have hFE (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hn : dualEnergy g hgn p = 0) :=
    eq_of_positive_homogeneous_of_unitNull_trace r g hgn E F hhom hFhom he hp hn
  refine ⟨F, hF, hFpos, hFhom, hFE, fun p hp => ?_⟩
  rw [actualHamiltonDerivative_of_eq_null_trace_at_unit r g hg hgn hgs E F hF hFE hp (hE p hp)]
  exact hH p hp
end Burnett.Geometry.ActualTestLift

namespace Burnett.Geometry.ActualTestLift

open Set MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- The actual full-cotangent transport conclusion from a genuine positive null first integral. -/
theorem actual_full_transport_of_null_firstIntegral [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g)
    (μ : Measure (cotangentUnitNull r g hgn)) [IsLocallyFiniteMeasure μ]
    (ht : HasActualUnitTransport r g hgn μ)
    (E : CotangentBundle M → ℝ)
    (hE : ∀ p ∈ cotangentUnitNull r g hgn, ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p)
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < E p)
    (hhom : ∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 →
      ∀ t > (0 : ℝ), E (cotangentScale t p) = t * E p)
    (hH : ∀ p ∈ cotangentUnitNull r g hgn, actualHamiltonDerivative g E p = 0) :
    ∃ s : CotangentBundle M → ℝ, ∃ hspos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent ∧
      (∀ p ∈ cotangentUnitNull r g hgn, s p = (E p)⁻¹) ∧
      (∀ b : CotangentBundle M → ℝ,
        ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent →
        HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.val) →
        Integrable (fun p : puncturedCotangent (M := M) => actualHamiltonDerivative g b p.val)
          (actualWeightedLift r g hgn s hspos μ) ∧
        (∫ p : puncturedCotangent (M := M), actualHamiltonDerivative g b p.val
          ∂actualWeightedLift r g hgn s hspos μ) = 0) := by
  obtain ⟨F, hF, hFpos, hFhom, hFE, hFH⟩ :=
    exists_positive_degreeOne_firstIntegral_extension r g hg hgn hgs E hE hpos hhom hH
  let s := fun p => (F p)⁻¹
  have hS : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent :=
    hF.inv₀ (fun p hp => (hFpos p hp).ne')
  have hspos (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hgn) : 0 < s p :=
    inv_pos.mpr (hFpos p (cotangentUnitNull_covector_ne_zero r g hgn hp))
  have hI (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hgn) :
      scaleInvariantInChart r g p.1 s p :=
    scaleInvariantInChart_of_degreeOneEnergy r g hgn p.1 F hF hFhom
      (mem_chart_source CoordinateSpace p.1) hp
      (hFpos p (cotangentUnitNull_covector_ne_zero r g hgn hp)) (hFH p hp)
  refine ⟨s, hspos, hS, ?_, actual_full_transport_of_invariant_scale r g hg hgn hgs μ s hS hspos hI ht⟩
  intro p hp
  unfold s
  rw [hFE p (cotangentUnitNull_covector_ne_zero r g hgn hp) hp.2]

end Burnett.Geometry.ActualTestLift
