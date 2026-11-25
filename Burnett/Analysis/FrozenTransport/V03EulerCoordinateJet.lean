import Burnett.Analysis.FrozenTransport.V03EulerJetRemainder
import Burnett.Geometry.ConnectionDifference

/-! Identifying the finite Euler jet polynomial with the ordinary coordinate
divergence Euler expression of the actual density. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Filter Set Burnett.Analysis.TransportWardSymbol Burnett.Geometry.ConnectionDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

local notation "E" => CoordinateSpace

/-- Formation of the actual metric from the chosen fixed symmetric field basis. -/
def assembleMetricComponents {ι : Type*} [Fintype ι] (S : ι → Mat) : (ι → ℝ) →L[ℝ] Mat :=
  ∑ i, ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (S i))

theorem assembleMetricComponents_apply {ι : Type*} [Fintype ι]
    (S : ι → Mat) (z : ι → ℝ) :
    assembleMetricComponents S z = ∑ i, z i • S i := by
  simp only [assembleMetricComponents, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

/-- The spatial coordinate derivatives of the original field. -/
def coordinateMetricFirstJet {ι : Type*} [Fintype ι] (k : E → ι → ℝ)
    (x : E) (s : ActionSlot ι) : ℝ :=
  fderiv ℝ k x (coordinateBasis s.1) s.2

/-- The second jet with the order of the Euler divergence preserved. -/
def coordinateMetricSecondJet {ι : Type*} [Fintype ι] (k : E → ι → ℝ)
    (x : E) (a : Fin 4) (s : ActionSlot ι) : ℝ :=
  fderiv ℝ (fun y => coordinateMetricFirstJet k y s) x (coordinateBasis a)

/-- The coordinate Euler divergence of the actual first-order density. -/
def coordinateDensityEuler {ι : Type*} [Fintype ι] (S : ι → Mat) (k : E → ι → ℝ)
    (x : E) (i : ι) : ℝ :=
  (∑ s, ∑ t, ((1 / 2) * fderiv ℝ (metricActionCoefficient S s t)
      (assembleMetricComponents S (k x)) (S i)) * coordinateMetricFirstJet k x s *
        coordinateMetricFirstJet k x t) -
    ∑ a, ∑ t, fderiv ℝ (fun y => metricActionCoefficient S (a, i) t
      (assembleMetricComponents S (k y)) * coordinateMetricFirstJet k y t) x (coordinateBasis a)

private theorem contDiffOn_coordinateMetricFirstJet {ι : Type*} [Fintype ι]
    {U : Set E} (hU : IsOpen U) (k : E → ι → ℝ) (hk : ContDiffOn ℝ ∞ k U)
    (t : ActionSlot ι) : ContDiffOn ℝ ∞ (fun y => coordinateMetricFirstJet k y t) U :=
  (contDiff_apply ℝ ℝ t.2).contDiffOn.comp
    ((hk.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const) (fun _ _ => mem_univ _)

theorem coordinateDensityEuler_eq_metricEulerAtJet {ι : Type*} [Fintype ι] (S : ι → Mat)
    {U : Set E} (hU : IsOpen U) (k : E → ι → ℝ) (hk : ContDiffOn ℝ ∞ k U)
    (x : E) (hx : x ∈ U) (hdet : (assembleMetricComponents S (k x)).det ≠ 0) (i : ι) :
    coordinateDensityEuler S k x i =
      metricEulerAtJet S (assembleMetricComponents S (k x)) (coordinateMetricFirstJet k x)
        (coordinateMetricSecondJet k x) i := by
  let G := assembleMetricComponents S (k x)
  let p := coordinateMetricFirstJet k x
  let q := coordinateMetricSecondJet k x
  let D (a : Fin 4) (j : ι) (t : ActionSlot ι) :=
    fderiv ℝ (metricActionCoefficient S (a, i) t) G (S j) * p (a, j) * p t
  have hkd := (hk.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hf (a : Fin 4) (t : ActionSlot ι) :
      fderiv ℝ (fun y => metricActionCoefficient S (a, i) t (assembleMetricComponents S (k y)) *
        coordinateMetricFirstJet k y t) x (coordinateBasis a) =
        (∑ j, D a j t) + metricActionCoefficient S (a, i) t G * q a t := by
    have hc := ((contDiffOn_metricActionCoefficient S (a, i) t).contDiffAt
      (isOpen_nonsingularMetricDomain.mem_nhds hdet)).differentiableAt (by simp)
    have hτ := ((contDiffOn_coordinateMetricFirstJet hU k hk t).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
    have hc' := hc.hasFDerivAt.comp x
      ((assembleMetricComponents S).hasFDerivAt.comp x hkd.hasFDerivAt)
    have hflux := DFunLike.congr_fun (hc'.fun_mul hτ.hasFDerivAt).fderiv (coordinateBasis a)
    simp only [Function.comp_apply] at hflux
    rw [hflux]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, assembleMetricComponents_apply, map_sum, map_smul, D, G, p, q, coordinateMetricSecondJet,
      coordinateMetricFirstJet, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum :
      (∑ a, ∑ t, fderiv ℝ (fun y => metricActionCoefficient S (a, i) t
        (assembleMetricComponents S (k y)) * coordinateMetricFirstJet k y t) x (coordinateBasis a)) =
      (∑ s : ActionSlot ι, ∑ t, D s.1 s.2 t) +
        ∑ a, ∑ t, metricActionCoefficient S (a, i) t G * q a t := by
    have hProd : (∑ s : ActionSlot ι, ∑ t, D s.1 s.2 t) = ∑ a, ∑ j, ∑ t, D a j t := by
      simp only [Fintype.sum_prod_type]
    simp only [hf, Finset.sum_add_distrib, hProd]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  unfold coordinateDensityEuler metricEulerAtJet
  rw [hsum]
  change (∑ s, ∑ t, ((1 / 2) * fderiv ℝ (metricActionCoefficient S s t) G (S i)) * p s * p t) -
      ((∑ s : ActionSlot ι, ∑ t, D s.1 s.2 t) +
        ∑ a, ∑ t, metricActionCoefficient S (a, i) t G * q a t) =
    (∑ s, ∑ t, metricEulerLowerCoefficient S i s t G * p s * p t) -
      ∑ a, ∑ t, metricActionCoefficient S (a, i) t G * q a t
  simp only [metricEulerLowerCoefficient, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, D]
  ring

private theorem coordinateMetricFirstJet_line {ι : Type*} [Fintype ι]
    (g h : E → ι → ℝ) (x : E) (u : ℝ) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    coordinateMetricFirstJet (fun y => g y + u • h y) x =
      fieldSegment (coordinateMetricFirstJet g x) (coordinateMetricFirstJet h x) u := by
  have hd := (hg.hasFDerivAt.fun_add (hh.hasFDerivAt.fun_const_smul u)).fderiv
  funext s
  simp only [coordinateMetricFirstJet, hd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, fieldSegment, Pi.add_apply, Pi.smul_apply]

private theorem coordinateMetricSecondJet_line {ι : Type*} [Fintype ι]
    {U : Set E} (hU : IsOpen U) (g h : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E) (hx : x ∈ U) (u : ℝ) :
    coordinateMetricSecondJet (fun y => g y + u • h y) x =
      fieldSegment (coordinateMetricSecondJet g x) (coordinateMetricSecondJet h x) u := by
  funext a s
  have hg₁ := ((contDiffOn_coordinateMetricFirstJet hU g hg s).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have hh₁ := ((contDiffOn_coordinateMetricFirstJet hU h hh s).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => coordinateMetricFirstJet (fun z => g z + u • h z) y s) =ᶠ[𝓝 x]
      fun y => coordinateMetricFirstJet g y s + u • coordinateMetricFirstJet h y s := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact congrFun (coordinateMetricFirstJet_line g h y u
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hh.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))) s
  have hd := (hg₁.hasFDerivAt.fun_add (hh₁.hasFDerivAt.fun_const_smul u)).fderiv
  simp only [coordinateMetricSecondJet, he.fderiv_eq, hd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, fieldSegment, Pi.add_apply, Pi.smul_apply]

/-- The same ordinary Euler expression at the actually perturbed metric, with
the lower remainder separated from the perturbed second derivative. -/
theorem coordinateDensityEulerRemainder_eq {ι : Type*} [Fintype ι] (S : ι → Mat)
    {U : Set E} (hU : IsOpen U) (g h : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E) (hx : x ∈ U) (i : ι)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (fieldSegment (assembleMetricComponents S (g x)) (assembleMetricComponents S (h x)) t).det ≠ 0) :
    let G := assembleMetricComponents S (g x)
    let H := assembleMetricComponents S (h x)
    quadraticPathRemainder (fun t => coordinateDensityEuler S (fun y => g y + t • h y) x i) =
      (∑ a, ∑ t, principalCoefficientRemainder (metricActionCoefficient S (a, i) t) G H *
          coordinateMetricSecondJet h x a t) +
        metricEulerJetLowerRemainder S G H (coordinateMetricFirstJet g x)
          (coordinateMetricFirstJet h x) (coordinateMetricSecondJet g x) i := by
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  let P := coordinateMetricFirstJet g x
  let dP := coordinateMetricFirstJet h x
  let Q := coordinateMetricSecondJet g x
  let dQ := coordinateMetricSecondJet h x
  let F (u : ℝ) := coordinateDensityEuler S (fun y => g y + u • h y) x i
  let J (u : ℝ) := metricEulerAtJet S (fieldSegment G H u) (fieldSegment P dP u) (fieldSegment Q dQ u) i
  have h0 : G.det ≠ 0 := by simpa only [fieldSegment, zero_smul, add_zero] using hseg 0 (by simp)
  have hEq (u : ℝ) (hu : (fieldSegment G H u).det ≠ 0) : F u = J u := by
    have hG : assembleMetricComponents S (g x + u • h x) = fieldSegment G H u := by
      simp only [map_add, map_smul, fieldSegment, G, H]
    have hg₀ := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hh₀ := (hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hline : ContDiffOn ℝ ∞ (fun y => g y + u • h y) U :=
      hg.add (hh.const_smul u)
    simpa only [J, F, P, Q, dP, dQ, hG, coordinateMetricFirstJet_line g h x u hg₀ hh₀,
      coordinateMetricSecondJet_line hU g h hg hh x hx u] using
      coordinateDensityEuler_eq_metricEulerAtJet S hU (fun y => g y + u • h y)
        hline x hx (by rw [hG]; exact hu) i
  have hopen : IsOpen (fieldSegment G H ⁻¹' nonsingularMetricDomain) :=
    isOpen_nonsingularMetricDomain.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hNear : F =ᶠ[𝓝 (0 : ℝ)] J := by
    filter_upwards [hopen.mem_nhds (hseg 0 (by simp))] with u hu
    exact hEq u hu
  have hR : quadraticPathRemainder F = quadraticPathRemainder J := by
    rw [quadraticPathRemainder, quadraticPathRemainder, hEq 0 (hseg 0 (by simp)),
      hEq 1 (hseg 1 (by simp)), hNear.deriv_eq, hNear.deriv.deriv_eq]
  exact hR.trans (metricEulerJetRemainder_eq S G H P dP Q dQ i h0)

end Burnett.V03
