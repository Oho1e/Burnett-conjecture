import Burnett.Analysis.CubicEnergy.CompleteEnergy.FieldAndCoefficientChecks
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview

private def firstCoordinate : E := EuclideanSpace.single (0 : Index) 1

private theorem fieldValue_continuous {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ) :
    Continuous (fieldValueArray z) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => (z j).continuous)

private theorem fullGradient_continuous {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ) :
    Continuous (euclideanFieldGradient z) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => (energyPartial k.1 (z k.2)).continuous)

private theorem derivative_slice_le_full {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (x : E) :
    ‖fieldValueArray (fun j => energyPartial 0 (z j)) x‖ ≤ ‖euclideanFieldGradient z x‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  change (∑ j : J, ‖energyPartial 0 (z j) x‖ ^ 2) ≤
    ∑ k : Index × J, ‖energyPartial k.1 (z k.2) x‖ ^ 2
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hNonneg (i : Index) (_ : i ∈ Finset.univ) :
      0 ≤ ∑ j : J, ‖energyPartial i (z j) x‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  exact Finset.single_le_sum hNonneg (Finset.mem_univ (0 : Index))

private theorem line_integral_eq_endpoint_sub {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (x : E) (length : ℝ) :
    (∫ t in (0 : ℝ)..length, fieldValueArray (fun j => energyPartial 0 (z j))
      (x + t • firstCoordinate)) =
    fieldValueArray z (x + length • firstCoordinate) - fieldValueArray z x := by
  let path (t : ℝ) : E := x + t • firstCoordinate
  have hc : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  let v := fieldValueArray (fun j => energyPartial 0 (z j))
  have hv : Continuous (v ∘ path) := (fieldValue_continuous _).comp hc
  ext j
  let proj : EuclideanSpace ℂ J →L[ℂ] ℂ := PiLp.proj 2 _ j
  change proj (∫ t in (0 : ℝ)..length, v (path t)) = z j (path length) - z j x
  have hvI : IntervalIntegrable (fun t => v (path t)) volume 0 length := hv.intervalIntegrable 0 length
  rw [← proj.intervalIntegral_comp_comm hvI]
  change (∫ t in (0 : ℝ)..length, energyPartial 0 (z j) (path t)) = _
  have hd (t : ℝ) : HasDerivAt path firstCoordinate t := by
    simpa only [path, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const firstCoordinate).const_add x
  have hz (t : ℝ) : HasDerivAt (fun s => z j (path s)) (energyPartial 0 (z j) (path t)) t := by
    simpa only [energyPartial, SchwartzMap.pderivCLM_apply, Function.comp_apply, firstCoordinate] using
      (((z j).differentiable (path t)).hasFDerivAt.comp_hasDerivAt t (hd t))
  have hint := ((energyPartial 0 (z j)).continuous.comp hc).intervalIntegrable (μ := volume) 0 length
  simpa only [path, zero_smul, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hz t) hint

/-- A fixed spatial line of length three radii bounds the value of the
original field by the integral of its original full Euclidean gradient. -/
theorem ball_field_norm_le_line_integral {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ)
    (c : E) (r : ℝ) (hr : 0 < r) (hz : tsupport (fieldValueArray z) ⊆ ball c r) (x : E) :
    ‖fieldValueArray z x‖ ≤
      ∫ t in (0 : ℝ)..(3 * r), ‖euclideanFieldGradient z (x + t • EuclideanSpace.single (0 : Index) 1)‖ := by
  let path (t : ℝ) : E := x + t • firstCoordinate
  let length := 3 * r
  have hLength : 0 ≤ length := by dsimp only [length]; positivity
  have hPath : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  let v := fieldValueArray (fun j => energyPartial 0 (z j))
  have hv := (fieldValue_continuous (fun j => energyPartial 0 (z j))).comp hPath
  have hgrad := (fullGradient_continuous z).comp hPath
  have zero_outside (y : E) (hy : y ∉ ball c r) : fieldValueArray z y = 0 :=
    Function.notMem_support.mp fun hs => hy (hz (subset_closure hs))
  change ‖fieldValueArray z x‖ ≤ ∫ t in (0 : ℝ)..length, ‖euclideanFieldGradient z (path t)‖
  by_cases hx : x ∈ ball c r
  · have hUnit : ‖firstCoordinate‖ = 1 := by simp [firstCoordinate]
    have hDist : dist (path length) x = length := by
      simp only [path, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hLength, hUnit, mul_one]
    have end_outside : path length ∉ ball c r := by
      intro hm
      have h1 := mem_ball.mp hx
      have h2 := mem_ball.mp hm
      have hTriangle := dist_triangle (path length) c x
      rw [dist_comm c x, hDist] at hTriangle
      dsimp only [length] at hTriangle
      linarith
    calc
      ‖fieldValueArray z x‖ = ‖∫ t in (0 : ℝ)..length, v (path t)‖ := by
        rw [line_integral_eq_endpoint_sub z x length, zero_outside _ end_outside, zero_sub, norm_neg]
      _ ≤ ∫ t in (0 : ℝ)..length, ‖v (path t)‖ := intervalIntegral.norm_integral_le_integral_norm hLength
      _ ≤ _ := intervalIntegral.integral_mono_on hLength (hv.norm.intervalIntegrable _ _)
        (hgrad.norm.intervalIntegrable _ _) fun t _ => derivative_slice_le_full z (path t)
  · rw [zero_outside x hx, norm_zero]
    exact intervalIntegral.integral_nonneg hLength fun t _ => norm_nonneg _

end Burnett.A03
