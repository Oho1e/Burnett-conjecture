import Burnett.Analysis.TransportWard.Weyl.QuadraticEulerAction
import Burnett.Analysis.TransportWard.Weyl.AffineProductSecondDerivative

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Function Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private affine_field_translate from Burnett.Analysis.TransportWard.Weyl.QuadraticEulerAction
open private coordinateMetricFirstJet_line from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private hasDerivAt_comp_fieldSegment hasDerivAt_first_dir from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

local notation "E₀" => CoordinateSpace

private theorem thirdVariationDensity_eq_second_time_deriv_weak
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E₀ → ι → ℝ) (x : E₀)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x)
    (hG : (assembleMetricComponents S (g x)).det ≠ 0) :
    coordinateActionThirdVariationDensity S g h k x =
      deriv (deriv (fun u : ℝ => coordinateWeakActionVariation S (fun y => g y + u • h y) k x)) 0 := by
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  have hOpen : IsOpen (fieldSegment G H ⁻¹' nonsingularMetricDomain) :=
    isOpen_nonsingularMetricDomain.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using hG
  unfold coordinateActionThirdVariationDensity
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hOpen.mem_nhds h0] with t ht
  have hT : (assembleMetricComponents S (g x + t • h x)).det ≠ 0 := by
    simpa only [fieldSegment, G, H, map_add, map_smul] using ht
  have hTime := hasDerivAt_coordinateWeakActionVariation S (fun y => g y + t • h y) h k x
    (hg.add (hh.fun_const_smul t)) hh hk hT
  have he : (fun u => coordinateWeakActionVariation S (fun y => (g y + t • h y) + u • h y) k x) =
      (fun u => coordinateWeakActionVariation S (fun y => g y + (t + u) • h y) k x) := by
    funext u
    rw [affine_field_translate g h t u]
  have hEq := hTime.deriv
  rw [he, deriv_comp_const_add (fun u => coordinateWeakActionVariation S (fun y => g y + u • h y) k x) t 0,
    add_zero] at hEq
  exact hEq.symm

/-- The terms with two differentiated perturbations and no background jet
are the cubic action, and every other term carries a background first jet. -/
theorem coordinateActionThirdVariationDensity_eq_cubic_and_background
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E₀ → ι → ℝ) (x : E₀)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x)
    (hG : (assembleMetricComponents S (g x)).det ≠ 0) :
    let G := assembleMetricComponents S (g x)
    let H := assembleMetricComponents S (h x)
    let K := assembleMetricComponents S (k x)
    let p := coordinateMetricFirstJet g x
    let q := coordinateMetricFirstJet h x
    let w := coordinateMetricFirstJet k x
    let C (s t : ActionSlot ι) := metricActionCoefficient S s t
    let CK (s t : ActionSlot ι) (A : Mat) := fderiv ℝ (C s t) A K
    coordinateActionThirdVariationDensity S g h k x =
      (∑ s, ∑ t, (fderiv ℝ (C s t) G K * q s * q t + 2 * fderiv ℝ (C s t) G H * w s * q t)) +
      (∑ s, ∑ t, (secondFDeriv (C s t) G H H * w s * p t +
        fderiv ℝ (CK s t) G H * (q s * p t + p s * q t) +
        (1 / 2 : ℝ) * secondFDeriv (CK s t) G H H * p s * p t)) := by
  intro G H K p q w C CK
  let J (s : ActionSlot ι) (t : ℝ) := p s + t * q s
  let L (s t : ActionSlot ι) (u : ℝ) := CK s t (fieldSegment G H u) * J s u * J t u
  let R (s t : ActionSlot ι) (u : ℝ) := C s t (fieldSegment G H u) * w s * J t u
  have hPath (u : ℝ) : coordinateWeakActionVariation S (fun y => g y + u • h y) k x =
      (1 / 2 : ℝ) * (∑ s, ∑ t, L s t u) + ∑ s, ∑ t, R s t u := by
    unfold coordinateWeakActionVariation
    rw [coordinateMetricFirstJet_line g h x u hg hh]
    simp only [C, CK, L, R, J, map_add, map_smul, fieldSegment, p, q, w, G, H, K]
    rfl
  have hCK (s t : ActionSlot ι) : ContDiffOn ℝ ∞ (CK s t) nonsingularMetricDomain :=
    ((contDiffOn_metricActionCoefficient S s t).fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)).clm_apply
      contDiffOn_const
  have hD₁ (s t : ActionSlot ι) := hasDerivAt_deriv_product_affine (CK s t) isOpen_nonsingularMetricDomain
    (hCK s t) G H hG (p s) (q s) (p t) (q t)
  have hD₂ (s t : ActionSlot ι) := hasDerivAt_deriv_product_affine (C s t) isOpen_nonsingularMetricDomain
    (contDiffOn_metricActionCoefficient S s t) G H hG (w s) 0 (p t) (q t)
  have hOpen : IsOpen (fieldSegment G H ⁻¹' nonsingularMetricDomain) :=
    isOpen_nonsingularMetricDomain.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using hG
  have hNear : deriv (fun u => coordinateWeakActionVariation S (fun y => g y + u • h y) k x) =ᶠ[𝓝 (0 : ℝ)]
      (fun u => (1 / 2 : ℝ) * (∑ s, ∑ t, deriv (L s t) u) + ∑ s, ∑ t, deriv (R s t) u) := by
    filter_upwards [hOpen.mem_nhds h0] with u hu
    have hL₀ (s t : ActionSlot ι) : DifferentiableAt ℝ (L s t) u :=
      (((hasDerivAt_comp_fieldSegment _ isOpen_nonsingularMetricDomain (hCK s t) G H u hu).mul
        (hasDerivAt_affine_real (p s) (q s) u)).mul (hasDerivAt_affine_real (p t) (q t) u)).differentiableAt
    have hR₀ (s t : ActionSlot ι) : DifferentiableAt ℝ (R s t) u :=
      (((hasDerivAt_comp_fieldSegment (C s t) isOpen_nonsingularMetricDomain
        (contDiffOn_metricActionCoefficient S s t) G H u hu).mul_const (w s)).mul
          (hasDerivAt_affine_real (p t) (q t) u)).differentiableAt
    have hD := ((HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
        HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => (hL₀ s t).hasDerivAt).const_mul (1 / 2 : ℝ)).add
      (HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
        HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => (hR₀ s t).hasDerivAt)
    rw [funext hPath]
    exact hD.deriv
  have hRderive (s t : ActionSlot ι) : HasDerivAt (deriv (R s t))
      (secondFDeriv (C s t) G H H * w s * p t + 2 * fderiv ℝ (C s t) G H * w s * q t) 0 := by
    simpa only [R,J, mul_zero, zero_mul, add_zero, zero_add, mul_assoc] using hD₂ s t
  have hFinal := ((HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
      HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => hD₁ s t).const_mul (1 / 2 : ℝ)).add
    (HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) => HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => hRderive s t)
  rw [thirdVariationDensity_eq_second_time_deriv_weak S g h k x hg hh hk hG, hNear.deriv_eq]
  rw [show deriv (fun u : ℝ => (1 / 2 : ℝ) * (∑ s, ∑ t, deriv (L s t) u) +
    ∑ s, ∑ t, deriv (R s t) u) 0 = _ from hFinal.deriv]
  have hSplit (s t : ActionSlot ι) :
      (1 / 2 : ℝ) * (secondFDeriv (CK s t) G H H * p s * p t +
        2 * fderiv ℝ (CK s t) G H * (q s * p t + p s * q t) + 2 * CK s t G * q s * q t) =
      fderiv ℝ (C s t) G K * q s * q t +
        (fderiv ℝ (CK s t) G H * (q s * p t + p s * q t) +
          (1 / 2 : ℝ) * secondFDeriv (CK s t) G H H * p s * p t) := by
    dsimp only [CK]
    ring
  simp only [Finset.mul_sum]
  simp only [hSplit]
  simp only [Finset.sum_add_distrib]
  ring

end Burnett.V03.Palatini
