import Burnett.Geometry.Cotangent.CauchyCrossingEnergy
import Burnett.Geometry.Cotangent.ChartLocalFlowSmoothness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter Metric
open scoped ContDiff Topology Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [HasContDiffBump E]

/-- A smooth chart field gives a jointly smooth family on one open product,
with the same original differential equation and initial conditions. -/
theorem exists_smooth_localFlow_of_contDiffOn {f : E → E} {x₀ : E} {V : Set E}
    (hV : IsOpen V) (hx₀ : x₀ ∈ V) (hf : ContDiffOn ℝ ∞ f V) :
    ∃ U : Set E, ∃ δ > (0 : ℝ), ∃ Φ : E × ℝ → E,
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-δ) δ) ∧
      MapsTo Φ (U ×ˢ Ioo (-δ) δ) V ∧ (∀ x ∈ U, Φ (x, 0) = x) ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => Φ (x, s)) (f (Φ (x, t))) t := by
  have hf₀ := (hf.contDiffAt (hV.mem_nhds hx₀)).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨U, δ, hδ, Φ, hU, hxU, hUV, hΦ, hMap, hInit, hODE⟩ :=
    exists_continuous_localFlow_of_contDiffAt hV hx₀ hf₀
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hprod : U ×ˢ Ioo (-δ) δ ∈ 𝓝 (x₀, (0 : ℝ)) :=
    (hU.prod isOpen_Ioo).mem_nhds ⟨hxU, hzero⟩
  have hΦ₀ := (hΦ (x₀, 0) ⟨hxU, hzero⟩).continuousAt hprod
  have hSmooth := eventually_contDiffAt_actual_chartLocalFlow hV hx₀ hf
    (hU.mem_nhds hxU) hδ Φ hΦ₀ hInit hODE
  have hNear : {p : E × ℝ | ContDiffAt ℝ ∞ Φ p ∧ p ∈ U ×ˢ Ioo (-δ) δ}
      ∈ 𝓝 (x₀, (0 : ℝ)) := hSmooth.and hprod
  rw [nhds_prod_eq] at hNear
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hNear
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hB
  let J : Set ℝ := Ioo (-r) r
  have hJB : J ⊆ B := by
    simpa only [J, Real.ball_eq_Ioo, zero_sub, zero_add] using hball
  have hzJ : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hr, hr⟩
  have hpA : x₀ ∈ interior A := mem_interior_iff_mem_nhds.mpr hA
  have hA' : interior A ⊆ U := by
    intro q hq
    have h : (q, (0 : ℝ)) ∈ A ×ˢ B := ⟨interior_subset hq, hJB hzJ⟩
    exact (hAB h).2.1
  have hpJ (p : E × ℝ) (hp : p ∈ interior A ×ˢ J) :=
    hAB (show p ∈ A ×ˢ B from ⟨interior_subset hp.1, hJB hp.2⟩)
  refine ⟨interior A, r, hr, Φ, isOpen_interior, hpA, hA'.trans hUV,
    fun p hp => (hpJ p hp).1.contDiffWithinAt, fun p hp => hMap (hpJ p hp).2,
    fun q hq => hInit q (hA' hq), ?_⟩
  intro q hq t ht
  exact hODE q (hA' hq) t (hpJ (q, t) ⟨hq, ht⟩).2.2

open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The genuine canonical Hamilton vector field yields smooth local phase
maps of actual trajectories through every punctured initial cotangent phase. -/
theorem exists_smooth_canonicalHamilton_localFlow (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) :
    ∃ U : Set (CotangentBundle M), ∃ δ > (0 : ℝ),
      ∃ Φ : CotangentBundle M × ℝ → CotangentBundle M,
      IsOpen U ∧ p ∈ U ∧ U ⊆ puncturedCotangent ∧
      ContMDiffOn (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞ Φ
        (U ×ˢ Ioo (-δ) δ) ∧ MapsTo Φ (U ×ˢ Ioo (-δ) δ) puncturedCotangent ∧
      ∀ q ∈ U, ∃ A : CanonicalTrajectory g q, A.domain = Ioo (-δ) δ ∧ A.curve = fun t => Φ (q, t) := by
  let c := p.proj
  have hpS : p ∈ cotangentSource c := mem_chart_source CoordinateSpace p.proj
  have hpT := cotangentChart_mem_punctured c p hpS hp
  have hField := contDiffOn_hamiltonVector_chartInverse g hg hn c
  obtain ⟨W, δ, hδ, F, hW, hpW, hWV, hF, hMap, hInit, hODE⟩ :=
    exists_smooth_localFlow_of_contDiffOn (isOpen_puncturedPhaseTarget c) hpT
      (hField.mono fun _ h => h.1)
  let U := cotangentSource c ∩ cotangentChart c ⁻¹' W
  let J : Set ℝ := Ioo (-δ) δ
  let G (qt : CotangentBundle M × ℝ) : Phase × ℝ := (cotangentChart c qt.1, qt.2)
  let Φ (qt : CotangentBundle M × ℝ) : CotangentBundle M := cotangentChartInverse c (F (G qt))
  have hU : IsOpen U :=
    (contMDiffOn_cotangentChart c).continuousOn.isOpen_inter_preimage (isOpen_cotangentSource c) hW
  have hGmap : MapsTo G (U ×ˢ J) (W ×ˢ J) := fun _ hz => ⟨hz.1.2, hz.2⟩
  have hC : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ, Phase) ∞ (cotangentChart c) (cotangentSource c) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_cotangentChart c
  have hG : ContMDiffOn (CotangentModelWithCorners.prod 𝓘(ℝ)) 𝓘(ℝ, Phase × ℝ) ∞ G (U ×ˢ J) :=
    (hC.comp contMDiffOn_fst (fun _ hz => hz.1.1)).prodMk_space contMDiffOn_snd
  have hInv : ContMDiffOn 𝓘(ℝ, Phase) CotangentModelWithCorners ∞
      (cotangentChartInverse c) (phaseTarget c) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_cotangentChartInverse c
  have hΦ : ContMDiffOn (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞ Φ (U ×ˢ J) :=
    hInv.comp (hF.contMDiffOn.comp hG hGmap) (fun z hz => (hMap (hGmap hz)).1)
  have hΦpun : MapsTo Φ (U ×ˢ J) puncturedCotangent :=
    fun _ hz => cotangentChartInverse_mem_punctured (hMap (hGmap hz))
  have hUpun : U ⊆ puncturedCotangent := by
    intro q hq
    have h := cotangentChartInverse_mem_punctured (hWV hq.2)
    rwa [cotangentChart_left_inv c hq.1] at h
  have hzero : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hδ, hδ⟩
  refine ⟨U, δ, hδ, Φ, hU, ⟨hpS, hpW⟩, hUpun, hΦ, hΦpun, ?_⟩
  intro q hq
  let η (t : ℝ) := F (cotangentChart c q, t)
  have hη : MapsTo η J (phaseTarget c) := by
    intro t ht
    have h : (cotangentChart c q, t) ∈ W ×ˢ J := ⟨hq.2, ht⟩
    exact (hMap h).1
  have hderiv (t : ℝ) (ht : t ∈ J) :
      HasDerivAt η (hamiltonVector (chartInverse g c) (η t)) t := hODE _ hq.2 t ht
  let γ (t : ℝ) := Φ (q, t)
  have hγ₀ : γ 0 = q := by
    change cotangentChartInverse c (F (cotangentChart c q, 0)) = q
    rw [hInit _ hq.2, cotangentChart_left_inv c hq.1]
  have hγChart : IsHamiltonCurveInChart g c γ J :=
    chartInverse_hamiltonCurve g c η J isOpen_Ioo hη hderiv
  let A : CanonicalTrajectory g q :=
    ⟨J, γ, isOpen_Ioo, ordConnected_Ioo, hzero, hγ₀,
      hamiltonCurve_canonical_integralOn g hg hn hs c γ J isOpen_Ioo hγChart
        (fun t ht => hΦpun ⟨hq, ht⟩)⟩
  exact ⟨A, rfl, rfl⟩

end Burnett.Geometry.CotangentHamiltonInitialFamily
