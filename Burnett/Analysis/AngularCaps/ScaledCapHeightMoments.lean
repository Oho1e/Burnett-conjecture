import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

/-- The L² part of the fixed L³ layer integral, with input height t/k. -/
theorem integrated_upper_square_at_scaled_height (g : X → ℝ) (hm : Measurable g)
    {k : ℝ} (hk : 0 < k) :
    (∫⁻ t in Ioi (0:ℝ), ∫⁻ x in {x | t < k*g x}, (ENNReal.ofReal (g x))^(2:ℕ) ∂μ) =
      ENNReal.ofReal k * ∫⁻ x, (ENNReal.ofReal (g x))^(3:ℕ) ∂μ := by
  let F := fun (t : ℝ) x => if t < k*g x then (ENNReal.ofReal (g x))^(2:ℕ) else 0
  have mF : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_lt measurable_fst ((hm.comp measurable_snd).const_mul k))
    · fun_prop
    · exact measurable_const
  have row (t : ℝ) :
      (∫⁻ x in {x | t < k*g x}, (ENNReal.ofReal (g x))^(2:ℕ) ∂μ) = ∫⁻ x, F t x ∂μ := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const (hm.const_mul k))]
    rfl
  have col (x : X) : (∫⁻ t in Ioi (0:ℝ), F t x) = ENNReal.ofReal k * (ENNReal.ofReal (g x))^(3:ℕ) := by
    change (∫⁻ t in Ioi (0:ℝ), (Iio (k*g x)).indicator (fun _ => (ENNReal.ofReal (g x))^(2:ℕ)) t) = _
    rw [lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero,
      ENNReal.ofReal_mul hk.le,pow_succ (ENNReal.ofReal (g x)) 2]
    ac_rfl
  simp_rw [row]
  rw [lintegral_lintegral_swap mF.aemeasurable]
  simp_rw [col]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The Lᵠ part of the fixed L³ layer integral, with the same input height. -/
theorem integrated_lower_power_at_scaled_height (g : X → ℝ) (hm : Measurable g)
    (hn : ∀ x, 0 ≤ g x) {k q : ℝ} (hk : 0 < k) (hq : 3 < q) :
    (∫⁻ t in Ioi (0:ℝ),
      (∫⁻ x in {x | k*g x ≤ t}, (ENNReal.ofReal (g x))^q ∂μ) * ENNReal.ofReal (t^(2-q))) =
      ENNReal.ofReal (k^(3-q)/(q-3)) * ∫⁻ x, (ENNReal.ofReal (g x))^(3:ℕ) ∂μ := by
  let Q (x : X) := (ENNReal.ofReal (g x))^q
  let v (t : ℝ) := ENNReal.ofReal (t^(2-q))
  let F (t : ℝ) (x : X) := if k*g x ≤ t then Q x * v t else 0
  have mF : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_le ((hm.comp measurable_snd).const_mul k) measurable_fst)
    · dsimp only [Q,v]
      fun_prop
    · exact measurable_const
  have row (t : ℝ) :
      (∫⁻ x in {x | k*g x ≤ t}, Q x ∂μ) * v t = ∫⁻ x, F t x ∂μ := by
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator (measurableSet_le (hm.const_mul k) measurable_const)]
    rfl
  have col (x : X) : (∫⁻ t in Ioi (0:ℝ), F t x) =
      ENNReal.ofReal (k^(3-q)/(q-3)) * (ENNReal.ofReal (g x))^(3:ℕ) := by
    rcases (hn x).eq_or_lt with hx | hx
    · simp [F,Q,← hx,ENNReal.zero_rpow_of_pos (by linarith : 0 < q)]
    have hkg := mul_pos hk hx
    have hS : Ici (k*g x) ∩ Ioi 0 = Ici (k*g x) := inter_eq_left.mpr (fun _ ht => hkg.trans_le ht)
    change (∫⁻ t in Ioi (0:ℝ), (Ici (k*g x)).indicator (fun t => Q x * v t) t) = _
    rw [lintegral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,hS,
      ← restrict_Ioi_eq_restrict_Ici,lintegral_const_mul' _ _ (by dsimp [Q]; finiteness)]
    have hInt : IntegrableOn (fun t : ℝ => t^(2-q)) (Ioi (k*g x)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hkg
    have hPos : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi (k*g x))] (fun t : ℝ => t^(2-q)) := by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hkg.trans ht).le _
    change (ENNReal.ofReal (g x))^q * (∫⁻ t in Ioi (k*g x), ENNReal.ofReal (t^(2-q))) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hPos,integral_Ioi_rpow_of_lt (by linarith) hkg,
      show 2-q+1 = 3-q by ring,ENNReal.ofReal_rpow_of_nonneg hx.le (by linarith : 0 ≤ q),
      ← ENNReal.ofReal_pow hx.le,← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hk.le _) (by linarith))]
    congr 1
    have eqpow : (g x)^q * (k*g x)^(3-q) = k^(3-q)*(g x)^3 := by
      rw [Real.mul_rpow hk.le hx.le,← mul_left_comm,← Real.rpow_add hx,show q+(3-q)=3 by ring]
      simp
    have hnz : q-3 ≠ 0 := (sub_pos.mpr hq).ne'
    have hnz' : 3-q ≠ 0 := (sub_neg.mpr hq).ne
    field_simp [hnz,hnz']
    linear_combination (3-q)*eqpow
  change (∫⁻ t in Ioi (0:ℝ), (∫⁻ x in {x | k*g x ≤ t}, Q x ∂μ)*v t) = _
  simp_rw [row]
  rw [lintegral_lintegral_swap mF.aemeasurable]
  simp_rw [col]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Burnett.Analysis.CapFourier
