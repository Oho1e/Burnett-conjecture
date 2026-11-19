import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit

open MeasureTheory Set
open Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Interval BigOperators

abbrev E := CoordinateSpace

/-- The low input-frequency cutoff on joint frequency space, with transition
between |η|=|ξ|/8 and |η|=|ξ|/4. -/
def lowWeight (η ξ : E) : ℝ :=
  Real.smoothTransition ((‖ξ‖^2 - 16 * ‖η‖^2) / ((48/65:ℝ) * (‖ξ‖^2 + ‖η‖^2)))

private theorem den_pos (η ξ : E) (h : η ≠ 0 ∨ ξ ≠ 0) :
    0 < (48/65:ℝ) * (‖ξ‖^2 + ‖η‖^2) := by
  apply mul_pos (by norm_num)
  rcases h with h|h
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr h))
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h)) (sq_nonneg _)

theorem lowWeight_eq_one {η ξ : E} (hξ : ξ ≠ 0) (h : 8*‖η‖ ≤ ‖ξ‖) :
    lowWeight η ξ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (den_pos η ξ (Or.inr hξ))).mpr
  nlinarith [sq_le_sq' (by linarith [norm_nonneg η] : -‖ξ‖ ≤ 8*‖η‖) h]

theorem lowWeight_eq_zero {η ξ : E} (h : ‖ξ‖ ≤ 4*‖η‖) : lowWeight η ξ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith [sq_le_sq' (by linarith [norm_nonneg ξ,norm_nonneg η] : -(4*‖η‖) ≤ ‖ξ‖) h]

theorem lowWeight_scale (t : ℝ) (ht : 0 < t) (η ξ : E) :
    lowWeight (t • η) (t • ξ) = lowWeight η ξ := by
  unfold lowWeight
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
  by_cases h : η = 0 ∧ ξ = 0
  · rcases h with ⟨rfl,rfl⟩
    simp
  · have hd := (den_pos η ξ (by tauto)).ne'
    have ht' := ht.ne'
    field_simp
theorem lowWeight_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : E × E => lowWeight p.1 p.2) {p | p ≠ 0} := by
  apply Real.smoothTransition.contDiff.comp_contDiffOn
  apply ContDiffOn.div
  · exact (contDiff_snd.norm_sq ℝ).contDiffOn.sub
      (contDiffOn_const.mul (contDiff_fst.norm_sq ℝ).contDiffOn)
  · exact contDiffOn_const.mul ((contDiff_snd.norm_sq ℝ).contDiffOn.add
      (contDiff_fst.norm_sq ℝ).contDiffOn)
  · intro p hp
    apply (den_pos p.1 p.2 _).ne'
    by_contra! h
    exact hp (Prod.ext h.1 h.2)

theorem segment_norm_lower {η ξ : E} (h : lowWeight η ξ ≠ 0) {t : ℝ} (ht : t ∈ Icc 0 1) :
    3*‖ξ‖/4 ≤ ‖ξ + t • η‖ ∧ ξ + t • η ≠ 0 := by
  have hsize : 4*‖η‖ < ‖ξ‖ := lt_of_not_ge (fun bad => h (lowWeight_eq_zero bad))
  have hlen := norm_sub_le (ξ + t • η) (t • η)
  rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hlen
  have hsm := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg η)
  constructor
  · linarith
  · apply norm_pos_iff.mp
    linarith [norm_nonneg η]

/-- The product-frequency multiplier stays outside the joint smooth symbols. -/
def angularComponent (b : E → ℝ) (j : Index) (ζ : E) : ℝ := b ζ * ζ j / ‖ζ‖^2

theorem sum_angularComponent (b : E → ℝ) (hb0 : b 0 = 0) (ζ : E) :
    ∑ j, ζ j * angularComponent b j ζ = b ζ := by
  by_cases hz : ζ = 0
  · simp [hz,hb0,angularComponent]
  · have hn : ‖ζ‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
    have hs : ∑ j, (ζ j)^2 = ‖ζ‖^2 := by
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    calc
      _ = ∑ j, (b ζ / ‖ζ‖^2) * (ζ j)^2 := Finset.sum_congr rfl (fun j _ => by unfold angularComponent; ring)
      _ = _ := by rw [← Finset.mul_sum,hs]; field_simp

def derivComponent (b : E → ℝ) (j : Index) (η ξ : E) : ℝ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ b (ξ + t • η) (coordinateBasis j)

private theorem apply_basis (L : E →L[ℝ] ℝ) (η : E) :
    L η = ∑ j, η j * L (coordinateBasis j) := by
  have h := congrArg L (coordinateBasis.sum_repr η)
  simpa only [map_sum,map_smul,smul_eq_mul,coordinateBasis,OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h.symm

theorem low_difference (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) {η ξ : E}
    (h : lowWeight η ξ ≠ 0) :
    (∑ j, η j * derivComponent b j η ξ) = b (η+ξ)-b ξ := by
  let u := fun t : ℝ => ξ + t • η
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  have hm : MapsTo u [[(0:ℝ),1]] {x | x ≠ 0} := by
    rw [uIcc_of_le zero_le_one]
    exact fun _ ht => (segment_norm_lower h ht).2
  have hu : Continuous u := continuous_const.add (continuous_id.smul continuous_const)
  have hd : ContinuousOn (fun t => fderiv ℝ b (u t)) [[(0:ℝ),1]] :=
    (hb.continuousOn_fderiv_of_isOpen ho (by simp)).comp hu.continuousOn hm
  have hint (j : Index) : IntervalIntegrable (fun t => η j * fderiv ℝ b (u t) (coordinateBasis j)) volume 0 1 :=
    (continuousOn_const.mul (hd.clm_apply continuousOn_const)).intervalIntegrable
  have hder (t : ℝ) (ht : t ∈ [[(0:ℝ),1]]) : HasDerivAt (b ∘ u) (fderiv ℝ b (u t) η) t := by
    have hdiff := ((hb.differentiableOn (by simp)) (u t) (hm ht)).differentiableAt (ho.mem_nhds (hm ht))
    have hpath : HasDerivAt u η t := by
      simpa [u] using ((hasDerivAt_id t).smul_const η).const_add ξ
    exact hdiff.hasFDerivAt.comp_hasDerivAt t hpath
  calc
    _ = ∑ j, ∫ t in (0:ℝ)..1, η j * fderiv ℝ b (u t) (coordinateBasis j) := by
      simp only [derivComponent,u,intervalIntegral.integral_const_mul]
    _ = ∫ t in (0:ℝ)..1, ∑ j, η j * fderiv ℝ b (u t) (coordinateBasis j) :=
      (intervalIntegral.integral_finset_sum (fun j _ => hint j)).symm
    _ = ∫ t in (0:ℝ)..1, fderiv ℝ b (u t) η := by
      apply intervalIntegral.integral_congr
      exact fun t _ => (apply_basis _ η).symm
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((hd.clm_apply continuousOn_const).intervalIntegrable)]
      simp [u,add_comm]

def lowSymbol (b : E → ℝ) (j : Index) (η ξ : E) : ℝ :=
  lowWeight η ξ * derivComponent b j η ξ

def productSymbol (j : Index) (η ξ : E) : ℝ :=
  (1 - lowWeight η ξ) * ((η+ξ) j) / ‖η‖

def inputSymbol (j : Index) (η ξ : E) : ℝ :=
  (1 - lowWeight η ξ) * (ξ j) / ‖η‖

/-- The joint multiplier of the commutator is recovered even at zero output frequency. -/
theorem commutator_symbol_eq (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hb0 : b 0 = 0)
    (η ξ : E) :
    b (η+ξ) - b ξ =
      (∑ j, η j * lowSymbol b j η ξ) +
      (∑ j, angularComponent b j (η+ξ) * productSymbol j η ξ * ‖η‖) -
      ∑ j, inputSymbol j η ξ * ‖η‖ * angularComponent b j ξ := by
  by_cases hη : η = 0
  · simp [hη,lowSymbol]
  have hn := norm_ne_zero_iff.mpr hη
  have low : (∑ j, η j * lowSymbol b j η ξ) = lowWeight η ξ * (b (η+ξ)-b ξ) := by
    by_cases h : lowWeight η ξ = 0
    · simp [lowSymbol,h]
    · rw [← low_difference b hb h,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold lowSymbol
      ring
  have high (z : E) : (∑ j, angularComponent b j z * ((1-lowWeight η ξ)*z j/‖η‖) * ‖η‖) =
      (1-lowWeight η ξ) * b z := by
    rw [← sum_angularComponent b hb0 z,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have right : (∑ j, inputSymbol j η ξ * ‖η‖ * angularComponent b j ξ) =
      (1-lowWeight η ξ)*b ξ := by
    rw [← high ξ]
    apply Finset.sum_congr rfl
    intro j _
    unfold inputSymbol
    ring
  rw [low,right]
  change _ = _ + (∑ j, angularComponent b j (η+ξ) * ((1-lowWeight η ξ)*(η+ξ) j/‖η‖) * ‖η‖) - _
  rw [high]
  ring

end Burnett.A02.FrequencySplit
