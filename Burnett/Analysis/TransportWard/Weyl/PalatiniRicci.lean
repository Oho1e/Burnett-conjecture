import Burnett.Analysis.TransportWard.Weyl.PalatiniSmoothPath

/-! The coordinate Palatini identity for the actual computed Levi–Civita path. -/

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Topology

local notation "E" => CoordinateSpace
local notation "P" => MetricParameterSpace

theorem hasDerivAt_coordinateConnectionJet_metricAffineVariation (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (x : E) (hx : x ∈ U) (d a b c : Index) :
    HasDerivAt (fun t => coordinateConnectionJet
        (coordinateConnectionFromMetric (metricAffineVariation g h t)) x d a b c)
      (coordinateConnectionJet (coordinateConnectionVariation g h) x d a b c) 0 := by
  let F (z : P) := coordinateConnectionFromMetric (metricAffineVariation g h z.1) z.2 a b c
  have hΩ := isOpen_nonsingularVariationDomain g h hU hg hh
  have hF : ContDiffOn ℝ ∞ F (nonsingularVariationDomain g h U) :=
    contDiffOn_coordinateConnection_metricAffineVariation_joint g h hU hg hh a b c
  have h0 := zero_mem_nonsingularVariationDomain g h x hx (hn x hx)
  have hD := hasDerivAt_coordinatePartial_parameterSlice F hΩ hF x h0 d
  have hEq : (fun y => deriv (fun t => F (t, y)) 0) =ᶠ[𝓝 x]
      fun y => coordinateConnectionVariation g h y a b c := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hg' : DifferentiableComponentsAt g y :=
      fun i j => ((hg i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    have hh' : DifferentiableComponentsAt h y :=
      fun i j => ((hh i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    exact (hasDerivAt_coordinateConnection_metricAffineVariation g h y hg' hh' (hn y hy) a b c).deriv
  exact hD.congr_deriv (DFunLike.congr_fun hEq.fderiv_eq (EuclideanSpace.single d 1))

/-- Palatini's identity using the true Ricci tensor of the computed connection
of the affine metric and the actual covariant derivative of its variation. -/
theorem hasDerivAt_coordinateRicci_metricAffineVariation (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hgs : ∀ y ∈ U, IsSymmetricTensor (g y)) (hhs : ∀ y ∈ U, IsSymmetricTensor (h y))
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (x : E) (hx : x ∈ U) (b c : Index) :
    HasDerivAt (fun t => coordinateRicci
        (coordinateConnectionFromMetric (metricAffineVariation g h t)) x b c)
      (covariantDivergenceDifference (coordinateConnectionFromMetric g x)
        (coordinateConnectionVariation g h x)
        (coordinateConnectionJet (coordinateConnectionVariation g h) x) b c) 0 := by
  let Γt (t : ℝ) := coordinateConnectionFromMetric (metricAffineVariation g h t)
  let Γ := coordinateConnectionFromMetric g x
  let C := coordinateConnectionVariation g h x
  let J := coordinateConnectionJet (coordinateConnectionVariation g h) x
  have hxN := hU.mem_nhds hx
  have hgd : DifferentiableComponentsAt g x :=
    fun i j => ((hg i j).contDiffAt hxN).differentiableAt (by simp)
  have hhd : DifferentiableComponentsAt h x :=
    fun i j => ((hh i j).contDiffAt hxN).differentiableAt (by simp)
  have hgJ := coordinateJet_symmetric g x (by
    filter_upwards [hxN] with y hy
    exact hgs y hy)
  have hhJ := coordinateJet_symmetric h x (by
    filter_upwards [hxN] with y hy
    exact hhs y hy)
  have hΓ : ∀ a i j, Γ a i j = Γ a j i :=
    christoffel_torsion_free (inverseMatrix (g x)) (coordinateJet g x) hgJ
  have hC : ∀ a i j, C a i j = C a j i := coordinateConnectionVariation_symmetric g h x hgJ hhJ
  have hΓ0 : Γt 0 x = Γ := by
    simp only [Γt, metricAffineVariation_zero, Γ]
  have hD (a i j : Index) : HasDerivAt (fun t => Γt t x a i j) (C a i j) 0 :=
    hasDerivAt_coordinateConnection_metricAffineVariation g h x hgd hhd (hn x hx) a i j
  have hJ (d a i j : Index) :
      HasDerivAt (fun t => coordinateConnectionJet (Γt t) x d a i j) (J d a i j) 0 :=
    hasDerivAt_coordinateConnectionJet_metricAffineVariation g h hU hg hh hn x hx d a i j
  have hCross (a e : Index) :
      HasDerivAt (fun t => Γt t x a a e * Γt t x e b c - Γt t x a c e * Γt t x e b a)
        (Γ a a e * C e b c + C a a e * Γ e b c - Γ a c e * C e b a - C a c e * Γ e b a) 0 := by
    have hp := ((hD a a e).mul (hD e b c)).sub ((hD a c e).mul (hD e b a))
    refine hp.congr_deriv ?_
    rw [hΓ0]
    ring
  have hSummand (a : Index) :
      HasDerivAt (fun t => coordinateConnectionJet (Γt t) x a a b c -
          coordinateConnectionJet (Γt t) x c a b a +
        ∑ e, (Γt t x a a e * Γt t x e b c - Γt t x a c e * Γt t x e b a))
        (covariantDerivative Γ C J a a b c - covariantDerivative Γ C J c a b a) 0 := by
    rw [covariant_contraction Γ C J hΓ hC]
    exact ((hJ a a b c).sub (hJ c a b a)).add
      (HasDerivAt.fun_sum fun e (_ : e ∈ Finset.univ) => hCross a e)
  exact HasDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) => hSummand a

theorem contDiffOn_coordinateRicci_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) (b c : Index) :
    ContDiffOn ℝ ∞ (fun z : P => coordinateRicci (coordinateConnectionFromMetric
      (metricAffineVariation g h z.1)) z.2 b c) (nonsingularVariationDomain g h U) := by
  let Ω := nonsingularVariationDomain g h U
  let Γ (z : P) := coordinateConnectionFromMetric (metricAffineVariation g h z.1) z.2
  have hΩ : IsOpen Ω := isOpen_nonsingularVariationDomain g h hU hg hh
  have hΓ (a i j : Index) : ContDiffOn ℝ ∞ (fun z : P => Γ z a i j) Ω :=
    contDiffOn_coordinateConnection_metricAffineVariation_joint g h hU hg hh a i j
  have hJ (d a i j : Index) :
      ContDiffOn ℝ ∞ (fun z : P =>
        coordinateConnectionJet (coordinateConnectionFromMetric (metricAffineVariation g h z.1)) z.2 d a i j) Ω := by
    let F (z : P) := Γ z a i j
    have hf : ContDiffOn ℝ ∞ F Ω := hΓ a i j
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) Ω := hf.fderiv_of_isOpen hΩ (by simp)
    have hw : ContDiffOn ℝ ∞ (fun _ : P => ((0 : ℝ), EuclideanSpace.single d (1 : ℝ))) Ω :=
      contDiffOn_const
    refine (hfd.clm_apply hw).congr ?_
    intro z hz
    exact coordinatePartial_spaceSlice_eq_fderiv F z.1 z.2 d
      ((hf.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
  unfold coordinateRicci ricci
  exact ContDiffOn.sum fun a _ => ((hJ a a b c).sub (hJ c a b a)).add
    (ContDiffOn.sum fun e _ => ((hΓ a a e).mul (hΓ e b c)).sub ((hΓ a c e).mul (hΓ e b a)))

theorem contDiffOn_einsteinHilbertDensity_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) :
    ContDiffOn ℝ ∞ (fun z : P => einsteinHilbertDensity (metricAffineVariation g h z.1) z.2)
      (nonsingularVariationDomain g h U) := by
  have hR := contDiffOn_coordinateRicci_metricAffineVariation_joint g h hU hg hh
  have hW := contDiffOn_inverseMetricDensity_metricAffineVariation_joint g h hg hh
  have hSum : ContDiffOn ℝ ∞ (fun z : P => ∑ b, ∑ c,
      inverseMetricDensity (metricAffineVariation g h z.1) z.2 b c *
        coordinateRicci (coordinateConnectionFromMetric (metricAffineVariation g h z.1)) z.2 b c)
      (nonsingularVariationDomain g h U) :=
    ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ => (hW b c).mul (hR b c)
  refine hSum.neg.congr ?_
  intro z _
  simp only [einsteinHilbertDensity, coordinateScalarCurvature, metricTrace, inverseMetricDensity,
    Finset.mul_sum, mul_assoc]

end Burnett.V03.Palatini
