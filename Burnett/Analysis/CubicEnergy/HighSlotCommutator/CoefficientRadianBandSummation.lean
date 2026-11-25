import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadianLimit

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Filter Finset
open scoped ENNReal Topology ContDiff BigOperators

def referenceCoefficientWindowPairSum
    (A : Joint → ℂ) (χ D f g h : SchwartzMap E ℂ) (t r : ℝ) (J : Finset ℕ) : ℂ :=
  ∑ j ∈ J, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
    (fun x => (windowTest χ D (r*dyadicScale t j) x).re) f g h

def referenceUnfilteredCoefficientPairSum
    (A : Joint → ℂ) (D f g h : SchwartzMap E ℂ) (t : ℝ) (J : Finset ℕ) : ℂ :=
  ∑ j ∈ J, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
    (fun x => (D x).re) f g h

private theorem coefficientScale_mul_right (r s : ℝ) (k : ℕ) :
    dyadicCoefficientScale (r*s) k = dyadicCoefficientScale r k*s := by
  unfold dyadicCoefficientScale
  ring

private theorem coefficientBand_weights_sum_bound {R : ℝ} (hR : 0≤R) (N : ℕ) :
    (∑ k ∈ range N, ENNReal.ofReal (dyadicCoefficientScale R (k+1))) ≤
      2*ENNReal.ofReal R := by
  have elem (k : ℕ) : dyadicCoefficientScale R (k+1) ≤ R*((1:ℝ)/2)^k := by
    have h : (0:ℝ) < 2^k := by positivity
    calc
      _ = (R/(2:ℝ)^k)/2 := by unfold dyadicCoefficientScale; rw [pow_succ,div_div]
      _ ≤ R/(2:ℝ)^k := div_le_self (div_nonneg hR h.le) (by norm_num)
      _ = _ := by simp only [one_mul,inv_pow,div_eq_mul_inv]
  have hr : (∑ k ∈ range N, dyadicCoefficientScale R (k+1)) ≤ R*2 := by
    calc
      _ ≤ ∑ k ∈ range N, R*((1:ℝ)/2)^k := sum_le_sum fun k _ => elem k
      _ = R*∑ k ∈ range N, ((1:ℝ)/2)^k := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hR
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by unfold dyadicCoefficientScale; positivity),
    ENNReal.ofReal_mul hR,ENNReal.ofReal_ofNat,mul_comm (ENNReal.ofReal R)] at h
  exact h

theorem referenceCoefficientWindowPairSum_telescoping
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (χ D f g h : SchwartzMap E ℂ) (t R : ℝ) (J : Finset ℕ) (N : ℕ) :
    referenceCoefficientWindowPairSum A χ D f g h t R J +
      (∑ m ∈ range N, referenceCoefficientWindowPairSum A (coefficientDyadicBandpass χ) D f g h t
        (dyadicCoefficientScale R (m+1)) J) =
    referenceCoefficientWindowPairSum A χ D f g h t (dyadicCoefficientScale R N) J := by
  unfold referenceCoefficientWindowPairSum
  rw [sum_comm (s := range N) (t := J),← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simpa only [coefficientScale_mul_right] using
    radianHighCommutatorPair_coefficient_telescoping A ha hA χ D f g h (dyadicScale t j) (R*dyadicScale t j) N

/-- The three actual radian coefficient estimates combine to the unfiltered
coefficient at finite operator-scale selections. The comparable budgets are
summed only over their fixed finite index set. The separated higher branch
is summed with its geometrically decaying ratio. -/
theorem referenceUnfilteredCoefficientPairSum_bound_of_branches
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (χ D f g h : SchwartzMap E ℂ) (hχ : χ 0=1)
    (t R : ℝ) (hR : 0≤R) (J : Finset ℕ) (K : ℕ)
    (M₀ M₁ mass : ℝ≥0∞) (B : ℕ → ℝ≥0∞)
    (low : ‖referenceCoefficientWindowPairSum A χ D f g h t R J‖ₑ ≤ M₀*mass)
    (comparable : ∀ m<K,
      ‖referenceCoefficientWindowPairSum A (coefficientDyadicBandpass χ) D f g h t
        (dyadicCoefficientScale R (m+1)) J‖ₑ ≤ B m*mass)
    (higher : ∀ m, K≤m →
      ‖referenceCoefficientWindowPairSum A (coefficientDyadicBandpass χ) D f g h t
        (dyadicCoefficientScale R (m+1)) J‖ₑ ≤ (M₁*ENNReal.ofReal (dyadicCoefficientScale R (m+1)))*mass) :
    ‖referenceUnfilteredCoefficientPairSum A D f g h t J‖ₑ ≤
      (M₀+(∑ m ∈ range K, B m)+M₁*(2*ENNReal.ofReal R))*mass := by
  let U m := referenceCoefficientWindowPairSum A (coefficientDyadicBandpass χ) D f g h t
    (dyadicCoefficientScale R (m+1)) J
  let L := referenceCoefficientWindowPairSum A χ D f g h t R J
  let W N := referenceCoefficientWindowPairSum A χ D f g h t (dyadicCoefficientScale R N) J
  have conv : Tendsto W atTop (𝓝 (referenceUnfilteredCoefficientPairSum A D f g h t J)) := by
    unfold W referenceCoefficientWindowPairSum referenceUnfilteredCoefficientPairSum
    apply tendsto_finset_sum
    intro j _
    simpa only [coefficientScale_mul_right] using
      tendsto_radianHighCommutatorPair_lowpass_coefficient A ha hA χ D f g h hχ
        (dyadicScale t j) (dyadicCoefficientScale (R*dyadicScale t j))
        (dyadicCoefficientScale_tendsto_zero _)
  refine le_of_tendsto' (continuous_enorm.continuousAt.tendsto.comp conv) fun N => ?_
  let s := (range N).filter (· < K)
  let u := (range N).filter (fun m => ¬ m<K)
  have hs : s ⊆ range K := fun m hm => mem_range.mpr (mem_filter.mp hm).2
  have hu : u ⊆ range N := fun m hm => (mem_filter.mp hm).1
  have split : (∑ m ∈ range N, ‖U m‖ₑ) = (∑ m ∈ s, ‖U m‖ₑ)+(∑ m ∈ u, ‖U m‖ₑ) :=
    (sum_filter_add_sum_filter_not (range N) (· < K) _).symm
  have cb : (∑ m ∈ s, ‖U m‖ₑ) ≤ (∑ m ∈ range K, B m)*mass := by
    rw [sum_mul]
    exact (sum_le_sum fun m hm => comparable m (mem_filter.mp hm).2).trans
      (sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => zero_le _)
  have hb : (∑ m ∈ u, ‖U m‖ₑ) ≤ (M₁*(2*ENNReal.ofReal R))*mass := by
    refine (sum_le_sum fun m hm => higher m (le_of_not_gt (mem_filter.mp hm).2)).trans ?_
    rw [← sum_mul,← mul_sum]
    exact mul_le_mul_right' (mul_le_mul_left'
      ((sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ => zero_le _)).trans
        (coefficientBand_weights_sum_bound hR N)) _) _
  have eq : L + (∑ m ∈ range N, U m) = W N :=
    referenceCoefficientWindowPairSum_telescoping A ha hA χ D f g h t R J N
  change ‖W N‖ₑ ≤ _
  rw [← eq]
  calc
    _ ≤ ‖L‖ₑ+∑ m ∈ range N, ‖U m‖ₑ :=
      (enorm_add_le _ _).trans (add_le_add_left (enorm_sum_le _ _) _)
    _ ≤ M₀*mass+((∑ m ∈ range K, B m)*mass+(M₁*(2*ENNReal.ofReal R))*mass) := by
      rw [split]
      exact add_le_add low (add_le_add cb hb)
    _ = _ := by simp only [add_mul,add_assoc]

end Burnett.A06
