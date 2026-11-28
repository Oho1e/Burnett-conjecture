import Burnett.Analysis.TransportWard.Weyl.ActualRemainderCoefficient
import Burnett.Analysis.TransportWard.Weyl.UniformEulerJetBounds

/-! Identification of the tested principal operator with the actual coordinate Euler remainder. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Filter Set MeasureTheory
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference (coordinateBasis)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise Topology

/-- The original real metric variation multiplied by the fixed physical
input cutoff and read in the same component ordering. -/
def chartMetricCutoffTest {ι : Type*} [Fintype ι] {U : Set Space} (hU : IsOpen U)
    (h : Space → ι → ℝ) (hh : ContDiffOn ℝ ∞ h U)
    (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U)
    (hρc : HasCompactSupport ρ) : CompactSchwartzComponents ι := by
  let q (i : ι) (x : Space) := ((ρ x * h x i : ℝ) : ℂ)
  have sq (i : ι) : ContDiff ℝ ∞ (q i) := Complex.ofRealCLM.contDiff.comp
    (Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hρ hρU
      ((contDiff_apply ℝ ℝ i).contDiffOn.comp hh (fun _ _ => mem_univ _)))
  have cq (i : ι) : HasCompactSupport (q i) :=
    (hρc.mul_right (f' := fun x => h x i)).comp_left Complex.ofReal_zero
  exact ⟨fun i => (cq i).toSchwartzMap (sq i), cq⟩

@[simp] theorem chartMetricCutoffTest_apply {ι : Type*} [Fintype ι] {U : Set Space} (hU : IsOpen U)
    (h : Space → ι → ℝ) (hh : ContDiffOn ℝ ∞ h U)
    (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U)
    (hρc : HasCompactSupport ρ) (i : ι) (x : Space) :
    (chartMetricCutoffTest hU h hh ρ hρ hρU hρc).val i x = ((ρ x * h x i : ℝ) : ℂ) := rfl

/-- Taking the inner input cutoff after the outer cutoff gives exactly the
inner-cutoff original field. The equality is independent of the quantization. -/
theorem chartMetricCutoffTest_inner_mul_eq {ι : Type*} [Fintype ι] {U : Set Space} (hU : IsOpen U)
    (h : Space → ι → ℝ) (hh : ContDiffOn ℝ ∞ h U)
    (θ ρ : Space → ℝ) (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ)
    (hθU : tsupport θ ⊆ U) (hρU : tsupport ρ ⊆ U)
    (hθc : HasCompactSupport θ) (hρc : HasCompactSupport ρ)
    (hPlateau : ∀ x, θ x ≠ 0 → ρ x = 1) (i : ι) (x : Space) :
    (θ x : ℂ) * (chartMetricCutoffTest hU h hh ρ hρ hρU hρc).val i x =
      (chartMetricCutoffTest hU h hh θ hθ hθU hθc).val i x := by
  simp only [chartMetricCutoffTest_apply, ← Complex.ofReal_mul]
  by_cases hx : θ x = 0
  · simp [hx]
  · simp only [hPlateau x hx, one_mul]

private theorem fderiv_real_component_direction {ι : Type*} [Fintype ι] {h : Space → ι → ℝ}
    {x : Space} (hh : DifferentiableAt ℝ h x) (b : Fin 4) (j : ι) :
    fderiv ℝ (fun y => (h y j : ℂ)) x (coordinateDirection b) =
      (coordinateMetricFirstJet h x (b,j) : ℂ) := by
  let C : (ι → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
  have hd := (C.hasFDerivAt.comp x hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (h y j : ℂ)) x = _ at hd
  rw [hd]
  change ((fderiv ℝ h x (coordinateDirection b) j : ℝ) : ℂ) =
    ((fderiv ℝ h x (coordinateBasis b) j : ℝ) : ℂ)
  rw [show coordinateBasis b = coordinateDirection b from EuclideanSpace.basisFun_apply _ _ b]

private theorem contDiffOn_first_jet {ι : Type*} [Fintype ι] {U : Set Space} (hU : IsOpen U)
    {h : Space → ι → ℝ} (hh : ContDiffOn ℝ ∞ h U) (b : Fin 4) (j : ι) :
    ContDiffOn ℝ ∞ (fun x => coordinateMetricFirstJet h x (b,j)) U :=
  (contDiff_apply ℝ ℝ j).contDiffOn.comp
    ((hh.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const) (fun _ _ => mem_univ _)

private theorem compactSecondJet_eq_of_original_germ {ι : Type*} [Fintype ι] {U : Set Space}
    (hU : IsOpen U) {h : Space → ι → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    (f : CompactSchwartzComponents ι) {x : Space} (hx : x ∈ U) (a b : Fin 4) (j : ι)
    (he : (fun y => f.val j y) =ᶠ[𝓝 x] fun y => (h y j : ℂ)) :
    (SchwartzMap.pderivCLM ℂ (coordinateDirection a)
      (SchwartzMap.pderivCLM ℂ (coordinateDirection b) (f.val j))) x =
      (coordinateMetricSecondJet h x a (b,j) : ℂ) := by
  have hgerm :
      (fun y => fderiv ℝ (f.val j : Space → ℂ) y (coordinateDirection b)) =ᶠ[𝓝 x]
        fun y => (coordinateMetricFirstJet h y (b,j) : ℂ) := by
    filter_upwards [eventually_eventually_nhds.mpr he, hU.mem_nhds hx] with y hy hyU
    have hy' : (fun z => f.val j z) =ᶠ[𝓝 y] fun z => (h z j : ℂ) := hy
    exact (congrArg (fun D : Space →L[ℝ] ℂ => D (coordinateDirection b)) hy'.fderiv_eq).trans
      (fderiv_real_component_direction ((hh.contDiffAt (hU.mem_nhds hyU)).differentiableAt
        (by simp)) b j)
  have hj := ((contDiffOn_first_jet hU hh b j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x hj.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (coordinateMetricFirstJet h y (b,j) : ℂ)) x = _ at hd
  rw [SchwartzMap.pderivCLM_apply]
  change fderiv ℝ (fun y => (SchwartzMap.pderivCLM ℂ (coordinateDirection b) (f.val j)) y)
    x (coordinateDirection a) = _
  simp only [SchwartzMap.pderivCLM_apply, hgerm.fderiv_eq, hd]
  change ((fderiv ℝ (fun y => coordinateMetricFirstJet h y (b,j)) x (coordinateDirection a) : ℝ) : ℂ) =
    ((fderiv ℝ (fun y => coordinateMetricFirstJet h y (b,j)) x (coordinateBasis a) : ℝ) : ℂ)
  rw [show coordinateBasis a = coordinateDirection a from EuclideanSpace.basisFun_apply _ _ a]

/-- The lower-order scalar field from the original Euler remainder, read in
the chart with its actual spatial first and background second jets. -/
def coordinateEulerLowerRemainder {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : Space → ι → ℝ) (i : ι) (x : Space) : ℝ :=
  metricEulerJetLowerRemainder S (assembleMetricComponents S (g x))
    (assembleMetricComponents S (h x)) (coordinateMetricFirstJet g x)
    (coordinateMetricFirstJet h x) (coordinateMetricSecondJet g x) i

/-- At every point in the output window the two independent cutoff functions
leave the actual Taylor coefficient and the actual two jets unchanged. -/
theorem coordinateEulerRemainder_eq_compactPrincipal_add_lower
    {ι : Type*} [Fintype ι] (S : ι → Mat) {U : Set Space} (hU : IsOpen U)
    (g h : Space → ι → ℝ) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ)
    (χA : Space → ℝ) {x : Space} (hx : x ∈ U) (hρone : ρ =ᶠ[𝓝 x] fun _ => 1) (hχAone : χA x = 1)
    (i : ι) (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (fieldSegment (assembleMetricComponents S (g x)) (assembleMetricComponents S (h x)) t).det ≠ 0) :
    let f := chartMetricCutoffTest hU h hh ρ hρ hρU hρc
    let G (y : Space) := assembleMetricComponents S (g y)
    let H (y : Space) := assembleMetricComponents S (h y)
    (quadraticPathRemainder (fun t => coordinateDensityEuler S (fun y => g y + t • h y) x i) : ℂ) =
      compactFinitePrincipalField (chartMetricRemainderCoefficient S χA G H) f i x +
        (coordinateEulerLowerRemainder S g h i x : ℂ) := by
  intro f G H
  have original (j : ι) : (fun y => f.val j y) =ᶠ[𝓝 x] fun y => (h y j : ℂ) := by
    filter_upwards [hρone] with y hy
    simp only [f, chartMetricCutoffTest_apply, show ρ y = 1 from hy, one_mul]
  have hSecond (a b : Fin 4) (j : ι) :=
    compactSecondJet_eq_of_original_germ hU hh f hx a b j (original j)
  rw [coordinateDensityEulerRemainder_eq S hU g h hg hh x hx i hseg]
  simp only [coordinateEulerLowerRemainder, Complex.ofReal_add]
  congr 1
  simp only [compactFinitePrincipalField, chartMetricRemainderCoefficient, hχAone, one_mul, hSecond,
    Complex.ofReal_sum, Fintype.sum_prod_type, Complex.ofReal_mul, G, H]

end Burnett.V03
