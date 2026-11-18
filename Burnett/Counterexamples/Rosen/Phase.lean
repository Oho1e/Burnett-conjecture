import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp

/-!
# Rosen multiscale example

The two-frequency phase, the local ODE and its limits.
-/

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Filter Set
open scoped Topology

def scaledSine (frequency u : ℝ) : ℝ := Real.sin (frequency * u) / frequency

def phase (slow fast u : ℝ) : ℝ := scaledSine slow u + scaledSine fast u

def oscillationPrimitive (slow fast u : ℝ) : ℝ :=
  scaledSine (2 * slow) u / 2 + scaledSine (2 * fast) u / 2 +
    scaledSine (slow - fast) u + scaledSine (slow + fast) u

theorem scaledSine_hasDerivAt (frequency u : ℝ) (hne : frequency ≠ 0) :
    HasDerivAt (scaledSine frequency) (Real.cos (frequency * u)) u := by
  have h := ((Real.hasDerivAt_sin (frequency * u)).comp u
    ((hasDerivAt_id u).const_mul frequency)).div_const frequency
  simpa [scaledSine, hne, Function.comp_def] using h

theorem phase_hasDerivAt (slow fast u : ℝ) (hslow : slow ≠ 0) (hfast : fast ≠ 0) :
    HasDerivAt (phase slow fast) (Real.cos (slow * u) + Real.cos (fast * u)) u :=
  (scaledSine_hasDerivAt slow u hslow).add (scaledSine_hasDerivAt fast u hfast)

theorem oscillationPrimitive_hasDerivAt (slow fast u : ℝ)
    (hslow : 0 < slow) (hfast : 2 * slow ≤ fast) :
    HasDerivAt (oscillationPrimitive slow fast) ((deriv (phase slow fast) u) ^ 2 - 1) u := by
  have hf : 0 < fast := by linarith
  have h₁ := (scaledSine_hasDerivAt (2 * slow) u (by positivity)).div_const 2
  have h₂ := (scaledSine_hasDerivAt (2 * fast) u (by positivity)).div_const 2
  have h₃ := scaledSine_hasDerivAt (slow - fast) u (by linarith)
  have h₄ := scaledSine_hasDerivAt (slow + fast) u (by linarith)
  have ht : (2 * slow) * u = 2 * (slow * u) := by ring
  have hs : (2 * fast) * u = 2 * (fast * u) := by ring
  rw [(phase_hasDerivAt slow fast u hslow.ne' hf.ne').deriv]
  convert (h₁.add h₂).add h₃ |>.add h₄ using 1
  rw [ht, hs, sub_mul, add_mul, Real.cos_sub, Real.cos_add,
    Real.cos_two_mul, Real.cos_two_mul]
  ring

theorem abs_scaledSine_le (frequency u : ℝ) :
    |scaledSine frequency u| ≤ 1 / |frequency| := by
  rw [scaledSine, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)

theorem abs_oscillationPrimitive_le (slow fast u : ℝ)
    (hslow : 0 < slow) (hfast : 2 * slow ≤ fast) :
    |oscillationPrimitive slow fast u| ≤ 3 / slow := by
  have hf : 0 < fast := by linarith
  have hd : 0 < fast - slow := by linarith
  have hs : 0 < slow + fast := by positivity
  have hbound (frequency : ℝ) (h : slow ≤ |frequency|) :
      |scaledSine frequency u| ≤ 1 / slow :=
    (abs_scaledSine_le frequency u).trans (one_div_le_one_div_of_le hslow h)
  have h₁ : |scaledSine (2 * slow) u| ≤ 1 / slow := hbound _ (by
    rw [abs_of_nonneg (by positivity)]; linarith)
  have h₂ : |scaledSine (2 * fast) u| ≤ 1 / slow := hbound _ (by
    rw [abs_of_nonneg (by positivity)]; linarith)
  have h₃ : |scaledSine (slow - fast) u| ≤ 1 / slow := hbound _ (by
    rw [abs_of_neg (by linarith)]; linarith)
  have h₄ : |scaledSine (slow + fast) u| ≤ 1 / slow := hbound _ (by
    rw [abs_of_pos hs]; linarith)
  unfold oscillationPrimitive
  calc
    |scaledSine (2 * slow) u / 2 + scaledSine (2 * fast) u / 2 +
      scaledSine (slow - fast) u + scaledSine (slow + fast) u| ≤
        |scaledSine (2 * slow) u / 2| + |scaledSine (2 * fast) u / 2| +
          |scaledSine (slow - fast) u| + |scaledSine (slow + fast) u| := by
            exact (abs_add_le _ _).trans (add_le_add_right
              ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)) _)
    _ ≤ 3 / slow := by
      rw [abs_div, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_eq_mul_inv, one_mul] at h₁ h₂ h₃ h₄ ⊢
      linarith

theorem two_mul_le_exp_of_nonneg (a : ℝ) (ha : 0 ≤ a) : 2 * a ≤ Real.exp a := by
  have h := Real.add_one_le_exp (a / 2)
  have hnonneg : 0 ≤ a / 2 + 1 := by positivity
  have hsq := mul_le_mul h h hnonneg (Real.exp_pos _).le
  have hx : a / 2 + a / 2 = a := by ring
  rw [← Real.exp_add, hx] at hsq
  nlinarith [sq_nonneg (a / 2 - 1)]

theorem exp_phase_primitive_bound (a u : ℝ) (ha : 0 < a) :
    |oscillationPrimitive a (Real.exp a) u| ≤ 3 / a :=
  abs_oscillationPrimitive_le a (Real.exp a) u ha (two_mul_le_exp_of_nonneg a ha.le)

theorem exp_phase_deriv_sq_mem_Icc (a u : ℝ) (ha : 0 < a) :
    (deriv (phase a (Real.exp a)) u) ^ 2 ∈ Icc (0 : ℝ) 4 := by
  rw [(phase_hasDerivAt a (Real.exp a) u ha.ne' (Real.exp_pos a).ne').deriv]
  let d := Real.cos (a * u) + Real.cos (Real.exp a * u)
  change d ^ 2 ∈ Icc (0 : ℝ) 4
  have habs : |d| ≤ 2 := (abs_add_le _ _).trans (by
    linarith [Real.abs_cos_le_one (a * u), Real.abs_cos_le_one (Real.exp a * u)])
  have hmul := mul_nonneg (sub_nonneg.mpr habs) (by positivity : 0 ≤ 2 + |d|)
  exact ⟨sq_nonneg d, by nlinarith [sq_abs d]⟩

theorem abs_intervalIntegral_phase_deriv_sq_sub_one (a left right : ℝ) (ha : 0 < a) :
    |∫ u in left..right, (deriv (phase a (Real.exp a)) u) ^ 2 - 1| ≤ 6 / a := by
  have he := Real.exp_pos a
  have hc : Continuous fun u => (deriv (phase a (Real.exp a)) u) ^ 2 - 1 := by
    simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' he.ne').deriv]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => oscillationPrimitive_hasDerivAt a (Real.exp a) u ha
      (two_mul_le_exp_of_nonneg a ha.le)) (hc.intervalIntegrable left right)]
  calc
    |oscillationPrimitive a (Real.exp a) right - oscillationPrimitive a (Real.exp a) left| ≤
        |oscillationPrimitive a (Real.exp a) right| + |oscillationPrimitive a (Real.exp a) left| :=
      abs_sub _ _
    _ ≤ 3 / a + 3 / a := add_le_add
      (exp_phase_primitive_bound a right ha) (exp_phase_primitive_bound a left ha)
    _ = 6 / a := by ring

theorem abs_intervalIntegral_weighted_phase_deriv_sq_sub_one
    (a left right : ℝ) (ha : 0 < a) (hab : left ≤ right)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    |∫ u in left..right, φ u * ((deriv (phase a (Real.exp a)) u) ^ 2 - 1)| ≤
      (3 / a) * (|φ right| + |φ left| + ∫ u in left..right, |deriv φ u|) := by
  let P := oscillationPrimitive a (Real.exp a)
  let q := fun u => (deriv (phase a (Real.exp a)) u) ^ 2 - 1
  have hPd (u : ℝ) : HasDerivAt P (q u) u :=
    oscillationPrimitive_hasDerivAt a (Real.exp a) u ha (two_mul_le_exp_of_nonneg a ha.le)
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun u => (hPd u).continuousAt
  have hq : Continuous q := by
    unfold q
    simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' (Real.exp_pos a).ne').deriv]
    fun_prop
  have hφ' := hφ.continuous_deriv_one
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hφ.continuous.continuousOn hP.continuousOn
    (fun u _ => (hφ.differentiable_one u).hasDerivAt) (fun u _ => hPd u)
    (hφ'.intervalIntegrable left right) (hq.intervalIntegrable left right)
  have hscale (u t : ℝ) : |t * P u| ≤ (3 / a) * |t| := by
    rw [abs_mul, mul_comm (3 / a)]
    exact mul_le_mul_of_nonneg_left (exp_phase_primitive_bound a u ha) (abs_nonneg t)
  have hintegral : |∫ u in left..right, deriv φ u * P u| ≤
      (3 / a) * ∫ u in left..right, |deriv φ u| := by
    calc
      |∫ u in left..right, deriv φ u * P u| ≤ ∫ u in left..right, |deriv φ u * P u| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun u => deriv φ u * P u) hab)
      _ ≤ ∫ u in left..right, (3 / a) * |deriv φ u| :=
        intervalIntegral.integral_mono_on hab ((hφ'.mul hP).abs.intervalIntegrable _ _)
          ((continuous_const.mul hφ'.abs).intervalIntegrable _ _)
          (fun u _ => hscale u (deriv φ u))
      _ = (3 / a) * (∫ u in left..right, |deriv φ u|) :=
        intervalIntegral.integral_const_mul (3 / a) _
  change |∫ u in left..right, φ u * q u| ≤ _
  rw [hibp]
  calc
    |φ right * P right - φ left * P left - ∫ u in left..right, deriv φ u * P u| ≤
        |φ right * P right| + |φ left * P left| + |∫ u in left..right, deriv φ u * P u| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ (3 / a) * |φ right| + (3 / a) * |φ left| +
           (3 / a) * (∫ u in left..right, |deriv φ u|) :=
      add_le_add (add_le_add (hscale right (φ right)) (hscale left (φ left))) hintegral
    _ = _ := by ring

theorem tendsto_weighted_phase_deriv_sq_sub_one
    (left right : ℝ) (hab : left ≤ right) (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n)) (C : ℝ)
    (hC : ∀ n, |φ n right| + |φ n left| + ∫ u in left..right, |deriv (φ n) u| ≤ C) :
    Tendsto (fun n : ℕ =>
      ∫ u in left..right, φ n u *
        ((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u) ^ 2 - 1)) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simp only [Real.norm_eq_abs]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    exact (abs_intervalIntegral_weighted_phase_deriv_sq_sub_one ((n : ℝ) + 1)
      left right hn hab (φ n) (hφ n)).trans
        (mul_le_mul_of_nonneg_left (hC n) (by positivity))
  · have hdecay := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3 : ℝ)).mul_const C
    simpa only [div_eq_mul_inv, one_mul, mul_zero, zero_mul] using hdecay

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

theorem phase_second_deriv (a b u : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    deriv (deriv (phase a b)) u = -(a * Real.sin (a * u) + b * Real.sin (b * u)) := by
  have hd : deriv (phase a b) = fun v => Real.cos (a * v) + Real.cos (b * v) :=
    funext fun v => (phase_hasDerivAt a b v ha hb).deriv
  rw [hd]
  have hd₁ := (Real.hasDerivAt_cos (a * u)).comp u ((hasDerivAt_id u).const_mul a)
  have hd₂ := (Real.hasDerivAt_cos (b * u)).comp u ((hasDerivAt_id u).const_mul b)
  convert (hd₁.add hd₂).deriv using 1
  ring

theorem phase_lower_at_slow_peak (a b : ℝ) (ha : 0 < a) (hab : 2 * a ≤ b) :
    1 / (2 * a) ≤ phase a b (Real.pi / (2 * a)) := by
  have h2a : 0 < 2 * a := by positivity
  have hb : 0 < b := h2a.trans_le hab
  have harg : a * (Real.pi / (2 * a)) = Real.pi / 2 := by
    field_simp [ha.ne']
  have hlow : -(1 / b) ≤ Real.sin (b * (Real.pi / (2 * a))) / b := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (Real.neg_one_le_sin _) hb.le
  calc
    1 / (2 * a) = 1 / a - 1 / (2 * a) := by
      field_simp [ha.ne']
      ring
    _ ≤ 1 / a - 1 / b := sub_le_sub_left (one_div_le_one_div_of_le h2a hab) _
    _ = 1 / a + -(1 / b) := by ring
    _ ≤ 1 / a + Real.sin (b * (Real.pi / (2 * a))) / b := add_le_add_left hlow _
    _ = phase a b (Real.pi / (2 * a)) := by
      simp only [phase, scaledSine, harg, Real.sin_pi_div_two]

theorem abs_phase_second_deriv_lower_at_fast_peak (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    b ≤ |deriv (deriv (phase a b)) (Real.pi / (2 * b))| := by
  have hb : 0 < b := ha.trans_le hab
  have harg : b * (Real.pi / (2 * b)) = Real.pi / 2 := by
    field_simp [hb.ne']
  have hπ : 0 < Real.pi := Real.pi_pos
  have haπ : a * (Real.pi / (2 * b)) ≤ Real.pi := by
    have hs := mul_le_mul_of_nonneg_right hab (by positivity : 0 ≤ Real.pi / (2 * b))
    rw [harg] at hs
    linarith
  have ha0 : 0 ≤ a * (Real.pi / (2 * b)) := by positivity
  have hslow : 0 ≤ a * Real.sin (a * (Real.pi / (2 * b))) :=
    mul_nonneg ha.le (Real.sin_nonneg_of_nonneg_of_le_pi ha0 haπ)
  rw [phase_second_deriv a b _ ha.ne' hb.ne', harg, Real.sin_pi_div_two,
    mul_one, abs_neg, abs_of_nonneg (add_nonneg hslow hb.le)]
  linarith

theorem exp_phase_peak_bounds (a : ℝ) (ha : 0 < a) :
    1 / (2 * a) ≤ phase a (Real.exp a) (Real.pi / (2 * a)) ∧
    Real.exp a ≤ |deriv (deriv (phase a (Real.exp a))) (Real.pi / (2 * Real.exp a))| := by
  have hab := two_mul_le_exp_of_nonneg a ha.le
  exact ⟨phase_lower_at_slow_peak a (Real.exp a) ha hab,
    abs_phase_second_deriv_lower_at_fast_peak a (Real.exp a) ha (by linarith)⟩

end Burnett.RosenMultiscale

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Set Metric Filter
open scoped Topology

def odeField (q : ℝ → ℝ) (t : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (2 * state.2, -(q t * state.1) / 2)

theorem odeField_lipschitz (q : ℝ → ℝ) (t : ℝ) (hq : q t ∈ Icc (0 : ℝ) 4) :
    LipschitzWith 2 (odeField q t) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  have hqabs : |q t| ≤ 4 := by simpa only [abs_of_nonneg hq.1] using hq.2
  have hfirst : |x.1 - y.1| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_left _ _
  have hsecond : |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
  simp only [odeField, Prod.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  apply max_le
  · rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hsecond (by norm_num)
  · have hfactor : -(q t * x.1) / 2 - -(q t * y.1) / 2 = (-(q t) / 2) * (x.1 - y.1) := by ring
    rw [hfactor, abs_mul, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |q t| / 2 * |x.1 - y.1| ≤ 2 * |x.1 - y.1| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst (by norm_num)

theorem odeField_norm_le (q : ℝ → ℝ) (t : ℝ) (hq : q t ∈ Icc (0 : ℝ) 4)
    (state : ℝ × ℝ) (hs : state ∈ closedBall ((1 : ℝ), (0 : ℝ)) 2) :
    ‖odeField q t state‖ ≤ 6 := by
  rw [mem_closedBall, Prod.dist_eq] at hs
  have h₁ : |state.1 - 1| ≤ 2 := by
    simpa only [Real.dist_eq] using (le_max_left _ _).trans hs
  have h₂ : |state.2| ≤ 2 := by
    simpa only [Real.dist_eq, sub_zero] using (le_max_right _ _).trans hs
  have h₁' : |state.1| ≤ 3 := by
    have hid : state.1 = (state.1 - 1) + 1 := by ring
    calc
      |state.1| = |(state.1 - 1) + 1| := congrArg abs hid
      _ ≤ |state.1 - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 3 := by rw [abs_one]; linarith
  simp only [odeField, Prod.norm_def, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hq.1]
  apply max_le
  · linarith
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      q t * |state.1| ≤ 4 * 3 := mul_le_mul hq.2 h₁' (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num

theorem exists_ode_pair (q : ℝ → ℝ) (hcont : Continuous q)
    (hq : ∀ t ∈ Icc (-(1 / 3) : ℝ) (1 / 3), q t ∈ Icc (0 : ℝ) 4) :
    ∃ state : ℝ → ℝ × ℝ, state 0 = (1, 0) ∧
      ∀ t ∈ Icc (-(1 / 3) : ℝ) (1 / 3),
        HasDerivWithinAt state (odeField q t (state t)) (Icc (-(1 / 3)) (1 / 3)) t := by
  let t₀ : Icc (-(1 / 3) : ℝ) (1 / 3) := ⟨0, by constructor <;> norm_num⟩
  have hPicard : IsPicardLindelof (odeField q) t₀ ((1 : ℝ), (0 : ℝ)) 2 0 6 2 := by
    constructor
    · intro t ht
      exact (odeField_lipschitz q t (hq t ht)).lipschitzOnWith
    · intro state _
      exact (show Continuous (fun t => odeField q t state) from
        continuous_const.prodMk (((hcont.mul continuous_const).neg).div_const 2)).continuousOn
    · intro t ht state hs
      exact odeField_norm_le q t (hq t ht) state hs
    · change 6 * max ((1 / 3 : ℝ) - 0) (0 - (-(1 / 3) : ℝ)) ≤ 2 - 0
      norm_num
  exact hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_scalar_ode_solution (q : ℝ → ℝ) (hcont : Continuous q)
    (hq : ∀ t ∈ Icc (-(1 / 3) : ℝ) (1 / 3), q t ∈ Icc (0 : ℝ) 4) :
    ∃ B : ℝ → ℝ, B 0 = 1 ∧ deriv B 0 = 0 ∧
      ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        ContDiffAt ℝ 2 B t ∧ deriv (deriv B) t = -(q t * B t) := by
  obtain ⟨state, h0, hstate⟩ := exists_ode_pair q hcont hq
  let S := Ioo (-(1 / 3) : ℝ) (1 / 3)
  let B : ℝ → ℝ := fun t => (state t).1
  let V : ℝ → ℝ := fun t => (state t).2
  have hOpen : IsOpen S := isOpen_Ioo
  have hderivatives (t : ℝ) (ht : t ∈ S) :
      HasDerivAt B (2 * V t) t ∧ HasDerivAt V (-(q t * B t) / 2) t := by
    have hd := (hstate t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    constructor
    · simpa [B, V, odeField] using hd.hasFDerivAt.fst.hasDerivAt
    · simpa [B, V, odeField] using hd.hasFDerivAt.snd.hasDerivAt
  have hbder (t : ℝ) (ht : t ∈ S) : deriv B t = 2 * V t := (hderivatives t ht).1.deriv
  have hb2der (t : ℝ) (ht : t ∈ S) : HasDerivAt (deriv B) (-(q t * B t)) t := by
    have hV := (hderivatives t ht).2.const_mul 2
    have hval : 2 * (-(q t * B t) / 2) = -(q t * B t) := by ring
    rw [hval] at hV
    refine hV.congr_of_eventuallyEq ?_
    filter_upwards [hOpen.mem_nhds ht] with u hu
    exact hbder u hu
  have hDiffB : DifferentiableOn ℝ B S := by
    intro t ht
    exact (hderivatives t ht).1.differentiableAt.differentiableWithinAt
  have hDiffB' : DifferentiableOn ℝ (deriv B) S := by
    intro t ht
    exact (hb2der t ht).differentiableAt.differentiableWithinAt
  have hB'' : ContinuousOn (deriv (deriv B)) S := by
    refine (hcont.continuousOn.mul hDiffB.continuousOn).neg.congr ?_
    intro t ht
    exact (hb2der t ht).deriv
  have hB1 : ContDiffOn ℝ 1 (deriv B) S := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hOpen).2
    exact ⟨hDiffB', by simp, contDiffOn_zero.mpr hB''⟩
  have hB2 : ContDiffOn ℝ 2 B S := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hOpen).2
    exact ⟨hDiffB, by simp, hB1⟩
  have h0S : (0 : ℝ) ∈ S := by constructor <;> norm_num
  refine ⟨B, congrArg Prod.fst h0, ?_, ?_⟩
  · rw [hbder 0 h0S]
    change 2 * (state 0).2 = 0
    rw [h0, mul_zero]
  · intro t ht
    have htS : t ∈ S := ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
    exact ⟨hB2.contDiffAt (hOpen.mem_nhds htS), (hb2der t htS).deriv⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set

theorem exists_phase_ode_solution (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ → ℝ, B 0 = 1 ∧ deriv B 0 = 0 ∧
      ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        ContDiffAt ℝ 2 B t ∧
        deriv (deriv B) t = -((deriv (phase a (Real.exp a)) t) ^ 2 * B t) := by
  apply exists_scalar_ode_solution
  · simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' (Real.exp_pos a).ne').deriv]
    fun_prop
  · intro t _
    exact exp_phase_deriv_sq_mem_Icc a t ha

end Burnett.RosenMultiscale

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Set
open scoped Interval

private theorem abs_sub_zero_le_of_hasDerivAt
    (f d : ℝ → ℝ) (r C : ℝ) (hr : 0 ≤ r)
    (hd : ∀ u ∈ Icc 0 r, HasDerivAt f (d u) u)
    (hc : ContinuousOn d (Icc 0 r)) (hbound : ∀ u ∈ Icc 0 r, |d u| ≤ C) :
    |f r - f 0| ≤ C * r := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by simpa only [uIcc_of_le hr] using hu))
    (hc.intervalIntegrable_of_Icc hr)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := r) (C := C) (f := d) (fun u hu => by
      rw [uIoc_of_le hr] at hu
      simpa only [Real.norm_eq_abs] using hbound u ⟨hu.1.le, hu.2⟩)
  rw [hFTC] at hnorm
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr] using hnorm

private theorem monotoneOn_of_hasDerivAt_nonneg
    {S : Set ℝ} {f d : ℝ → ℝ} (hS : Convex ℝ S)
    (hd : ∀ u ∈ S, HasDerivAt f (d u) u) (hsign : ∀ u ∈ S, 0 ≤ d u) :
    MonotoneOn f S := by
  apply monotoneOn_of_deriv_nonneg hS
  · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
  · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(hd u (interior_subset hu)).deriv]
    exact hsign u (interior_subset hu)

private theorem antitoneOn_of_hasDerivAt_nonpos
    {S : Set ℝ} {f d : ℝ → ℝ} (hS : Convex ℝ S)
    (hd : ∀ u ∈ S, HasDerivAt f (d u) u) (hsign : ∀ u ∈ S, d u ≤ 0) :
    AntitoneOn f S := by
  apply antitoneOn_of_deriv_nonpos hS
  · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
  · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(hd u (interior_subset hu)).deriv]
    exact hsign u (interior_subset hu)

private theorem contDiffAt_derive_once {B : ℝ → ℝ} {u : ℝ} {k : WithTop ℕ∞}
    (hB : ContDiffAt ℝ (k + 1) B u) : ContDiffAt ℝ k (deriv B) u := by
  have hf := hB.fderiv_right_succ
  simpa only [deriv] using hf.clm_apply
    (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ => (1 : ℝ)) u)

/-- Positive solutions and uniform derivative bounds on the positive half of the Rosen interval. -/
theorem local_ode_solution_bounds (B q : ℝ → ℝ)
    (hB : ∀ u ∈ Icc (0 : ℝ) (1 / 4), ContDiffAt ℝ 2 B u)
    (hBzero : B 0 = 1) (hDzero : deriv B 0 = 0)
    (hq : ∀ u ∈ Icc (0 : ℝ) (1 / 4), q u ∈ Icc (0 : ℝ) 4)
    (hODE : ∀ u ∈ Icc (0 : ℝ) (1 / 4), deriv (deriv B) u = -(q u * B u)) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 4),
      0 < B t ∧ B t ≤ 1 ∧ |deriv B t| ≤ 1 ∧ |deriv (deriv B) t| ≤ 4 := by
  let K := Icc (0 : ℝ) (1 / 4)
  have hzero : (0 : ℝ) ∈ K := by norm_num [K]
  have hD1 (u : ℝ) (hu : u ∈ K) : ContDiffAt ℝ 1 (deriv B) u :=
    contDiffAt_derive_once (k := 1) (by
      rw [show (1 : WithTop ℕ∞) + 1 = 2 by norm_num]
      exact hB u hu)
  have hD2 (u : ℝ) (hu : u ∈ K) : ContDiffAt ℝ 0 (deriv (deriv B)) u :=
    contDiffAt_derive_once (k := 0) (by simpa using hD1 u hu)
  have hFirst (u : ℝ) (hu : u ∈ K) : HasDerivAt B (deriv B u) u :=
    ((hB u hu).differentiableAt (by norm_num)).hasDerivAt
  have hSecond (u : ℝ) (hu : u ∈ K) : HasDerivAt (deriv B) (deriv (deriv B) u) u :=
    ((hD1 u hu).differentiableAt (by norm_num)).hasDerivAt
  have hContinuous : ContinuousOn B K := fun u hu => (hB u hu).continuousAt.continuousWithinAt
  have hContinuousFirst : ContinuousOn (deriv B) K :=
    fun u hu => (hD1 u hu).continuousAt.continuousWithinAt
  have hContinuousSecond : ContinuousOn (deriv (deriv B)) K :=
    fun u hu => (hD2 u hu).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, hzero⟩ hContinuous.abs
  let M := |B m|
  have hM : 0 ≤ M := abs_nonneg _
  have hMax (t : ℝ) (ht : t ∈ K) : |B t| ≤ M := isMaxOn_iff.mp hmax t ht
  have hD2Bound (t : ℝ) (ht : t ∈ K) : |deriv (deriv B) t| ≤ 4 * M := by
    rw [hODE t ht, abs_neg, abs_mul, abs_of_nonneg (hq t ht).1]
    exact mul_le_mul (hq t ht).2 (hMax t ht) (abs_nonneg _) (by norm_num)
  have hD1Bound (t : ℝ) (ht : t ∈ K) : |deriv B t| ≤ M := by
    have hsub : Icc (0 : ℝ) t ⊆ K := Icc_subset_Icc_right ht.2
    have h := abs_sub_zero_le_of_hasDerivAt (deriv B) (deriv (deriv B)) t (4 * M) ht.1
      (fun u hu => hSecond u (hsub hu)) (hContinuousSecond.mono hsub)
      (fun u hu => hD2Bound u (hsub hu))
    rw [hDzero, sub_zero] at h
    exact h.trans (by nlinarith [mul_nonneg hM (sub_nonneg.mpr ht.2)])
  have hNear (t : ℝ) (ht : t ∈ K) : |B t - 1| ≤ M / 4 := by
    have hsub : Icc (0 : ℝ) t ⊆ K := Icc_subset_Icc_right ht.2
    have h := abs_sub_zero_le_of_hasDerivAt B (deriv B) t M ht.1
      (fun u hu => hFirst u (hsub hu)) (hContinuousFirst.mono hsub)
      (fun u hu => hD1Bound u (hsub hu))
    rw [hBzero] at h
    exact h.trans (by nlinarith [mul_nonneg hM (sub_nonneg.mpr ht.2)])
  have hSmall : M ≤ 4 / 3 := by
    have h := abs_add_le (B m - 1) (1 : ℝ)
    rw [sub_add_cancel, abs_one] at h
    change M ≤ |B m - 1| + 1 at h
    linarith [hNear m hm]
  have hPos (t : ℝ) (ht : t ∈ K) : 0 < B t := by
    have h := (abs_le.mp (hNear t ht)).1
    linarith
  have hD2Nonpos (t : ℝ) (ht : t ∈ K) : deriv (deriv B) t ≤ 0 := by
    rw [hODE t ht]
    exact neg_nonpos.mpr (mul_nonneg (hq t ht).1 (hPos t ht).le)
  have hFirstAntitone : AntitoneOn (deriv B) K :=
    antitoneOn_of_hasDerivAt_nonpos (convex_Icc _ _) hSecond hD2Nonpos
  have hD1Nonpos (t : ℝ) (ht : t ∈ K) : deriv B t ≤ 0 := by
    simpa only [hDzero] using hFirstAntitone hzero ht ht.1
  have hBAntitone : AntitoneOn B K :=
    antitoneOn_of_hasDerivAt_nonpos (convex_Icc _ _) hFirst hD1Nonpos
  have hUpper (t : ℝ) (ht : t ∈ K) : B t ≤ 1 := by
    simpa only [hBzero] using hBAntitone hzero ht ht.1
  have hD2Final (t : ℝ) (ht : t ∈ K) : |deriv (deriv B) t| ≤ 4 := by
    rw [hODE t ht, abs_neg, abs_mul, abs_of_nonneg (hq t ht).1, abs_of_pos (hPos t ht)]
    exact (mul_le_mul (hq t ht).2 (hUpper t ht) (hPos t ht).le (by norm_num)).trans_eq (mul_one _)
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ K := Icc_subset_Icc_right ht.2
  have h := abs_sub_zero_le_of_hasDerivAt (deriv B) (deriv (deriv B)) t 4 ht.1
    (fun u hu => hSecond u (hsub hu)) (hContinuousSecond.mono hsub)
    (fun u hu => hD2Final u (hsub hu))
  rw [hDzero, sub_zero] at h
  exact ⟨hPos t ht, hUpper t ht, h.trans (by linarith [ht.2]), hD2Final t ht⟩

/-- The exact lower comparison with `cos (2u)` for a given local Rosen ODE solution. -/
theorem local_ode_cos_lower (B q : ℝ → ℝ)
    (hB : ∀ u ∈ Icc (0 : ℝ) (1 / 4), ContDiffAt ℝ 2 B u)
    (hBzero : B 0 = 1) (hDzero : deriv B 0 = 0)
    (hq : ∀ u ∈ Icc (0 : ℝ) (1 / 4), q u ∈ Icc (0 : ℝ) 4)
    (hODE : ∀ u ∈ Icc (0 : ℝ) (1 / 4), deriv (deriv B) u = -(q u * B u)) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 4), 0 < Real.cos (2 * t) ∧ Real.cos (2 * t) ≤ B t := by
  let K := Icc (0 : ℝ) (1 / 4)
  let C := fun t : ℝ => Real.cos (2 * t)
  let D := fun t : ℝ => -(2 * Real.sin (2 * t))
  let W := fun t : ℝ => C t * deriv B t - D t * B t
  have hzero : (0 : ℝ) ∈ K := by norm_num [K]
  have hbounds := local_ode_solution_bounds B q hB hBzero hDzero hq hODE
  have hCpos (t : ℝ) (ht : t ∈ K) : 0 < C t := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.one_le_pi_div_two]
  have hCd (t : ℝ) : HasDerivAt C (D t) t := by
    have h := (Real.hasDerivAt_cos (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
    convert h using 1; simp [D]; ring
  have hDd (t : ℝ) : HasDerivAt D (-(4 * C t)) t := by
    have h := ((Real.hasDerivAt_sin (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)).const_mul (-2)
    convert h using 1
    all_goals simp [C, D]
    all_goals ring
  have hFirst (t : ℝ) (ht : t ∈ K) : HasDerivAt B (deriv B t) t :=
    ((hB t ht).differentiableAt (by norm_num)).hasDerivAt
  have hSecond (t : ℝ) (ht : t ∈ K) : HasDerivAt (deriv B) (deriv (deriv B) t) t := by
    have h : ContDiffAt ℝ 1 (deriv B) t := contDiffAt_derive_once (k := 1)
      (by
        rw [show (1 : WithTop ℕ∞) + 1 = 2 by norm_num]
        exact hB t ht)
    exact (h.differentiableAt (by norm_num)).hasDerivAt
  have hWd (t : ℝ) (ht : t ∈ K) : HasDerivAt W ((4 - q t) * C t * B t) t := by
    have h := ((hCd t).mul (hSecond t ht)).sub ((hDd t).mul (hFirst t ht))
    convert h using 1
    rw [hODE t ht]
    ring
  have hWmono : MonotoneOn W K := monotoneOn_of_hasDerivAt_nonneg (convex_Icc _ _) hWd
    (fun t ht => mul_nonneg (mul_nonneg (sub_nonneg.mpr (hq t ht).2) (hCpos t ht).le)
      (hbounds t ht).1.le)
  have hWzero : W 0 = 0 := by simp [W, C, D, hDzero]
  have hWnonneg (t : ℝ) (ht : t ∈ K) : 0 ≤ W t := by
    simpa only [hWzero] using hWmono hzero ht ht.1
  have hRatio (t : ℝ) (ht : t ∈ K) :
      HasDerivAt (fun u => B u / C u) (W t / (C t)^2) t := by
    convert (hFirst t ht).div (hCd t) (hCpos t ht).ne' using 1
    congr 1
    unfold W
    ring
  have hRmono : MonotoneOn (fun u => B u / C u) K :=
    monotoneOn_of_hasDerivAt_nonneg (convex_Icc _ _) hRatio
      (fun t ht => div_nonneg (hWnonneg t ht) (sq_nonneg _))
  intro t ht
  have h := hRmono hzero ht ht.1
  change B 0 / C 0 ≤ B t / C t at h
  have hinit : B 0 / C 0 = 1 := by simp [C, hBzero]
  rw [hinit] at h
  exact ⟨hCpos t ht, by simpa only [one_mul] using (le_div_iff₀ (hCpos t ht)).mp h⟩

/-- Reflection transfers the comparison to the full closed Rosen interval. -/
theorem ode_cos_comparison (B q : ℝ → ℝ)
    (hB : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ContDiffAt ℝ 2 B u)
    (hBzero : B 0 = 1) (hDzero : deriv B 0 = 0)
    (hq : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), q u ∈ Icc (0 : ℝ) 4)
    (hODE : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), deriv (deriv B) u = -(q u * B u)) :
    ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      0 < Real.cos (2 * t) ∧ Real.cos (2 * t) ≤ B t ∧ B t ≤ 1 ∧
        |deriv B t| ≤ 1 ∧ |deriv (deriv B) t| ≤ 4 := by
  intro t ht
  by_cases ht0 : 0 ≤ t
  · have hsub : Icc (0 : ℝ) (1 / 4) ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) :=
      Icc_subset_Icc_left (by norm_num)
    have hs : t ∈ Icc (0 : ℝ) (1 / 4) := ⟨ht0, ht.2⟩
    have hc := local_ode_cos_lower B q (fun u hu => hB u (hsub hu)) hBzero hDzero
      (fun u hu => hq u (hsub hu)) (fun u hu => hODE u (hsub hu)) t hs
    have hb := local_ode_solution_bounds B q (fun u hu => hB u (hsub hu)) hBzero hDzero
      (fun u hu => hq u (hsub hu)) (fun u hu => hODE u (hsub hu)) t hs
    exact ⟨hc.1, hc.2, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  · let Br := fun u : ℝ => B (-u)
    let qr := fun u : ℝ => q (-u)
    have hNeg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (1 / 4)) :
        -u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) := by
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hBr (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (1 / 4)) : ContDiffAt ℝ 2 Br u :=
      (hB (-u) (hNeg u hu)).comp u contDiffAt_id.neg
    have hBrzero : Br 0 = 1 := by simpa [Br] using hBzero
    have hDr : deriv Br = fun u => -deriv B (-u) := funext (deriv_comp_neg B)
    have hDrzero : deriv Br 0 = 0 := by simp [hDr, hDzero]
    have hDr2 : deriv (deriv Br) = fun u => deriv (deriv B) (-u) := by
      rw [hDr]
      funext u
      rw [deriv.fun_neg, deriv_comp_neg, neg_neg]
    have hq' (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (1 / 4)) : qr u ∈ Icc (0 : ℝ) 4 :=
      hq (-u) (hNeg u hu)
    have hODE' (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (1 / 4)) :
        deriv (deriv Br) u = -(qr u * Br u) := by
      rw [hDr2]
      exact hODE (-u) (hNeg u hu)
    have ht' : -t ∈ Icc (0 : ℝ) (1 / 4) :=
      ⟨by linarith [lt_of_not_ge ht0], by linarith [ht.1]⟩
    have hc := local_ode_cos_lower Br qr hBr hBrzero hDrzero hq' hODE' (-t) ht'
    have hb := local_ode_solution_bounds Br qr hBr hBrzero hDrzero hq' hODE' (-t) ht'
    have hcos : Real.cos (2 * -t) = Real.cos (2 * t) := by rw [mul_neg, Real.cos_neg]
    exact ⟨by simpa only [hcos] using hc.1, by simpa only [hcos, Br, neg_neg] using hc.2,
      by simpa only [Br, neg_neg] using hb.2.1,
      by simpa only [hDr, neg_neg, abs_neg] using hb.2.2.1,
      by simpa only [hDr2, neg_neg] using hb.2.2.2⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set

theorem exists_phase_ode_solution_with_bounds (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ → ℝ, B 0 = 1 ∧ deriv B 0 = 0 ∧
      ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        ContDiffAt ℝ 2 B t ∧
        deriv (deriv B) t = -((deriv (phase a (Real.exp a)) t) ^ 2 * B t) ∧
        0 < Real.cos (2 * t) ∧ Real.cos (2 * t) ≤ B t ∧ B t ≤ 1 ∧
        |deriv B t| ≤ 1 ∧ |deriv (deriv B) t| ≤ 4 := by
  obtain ⟨B, hBzero, hDzero, hB⟩ := exists_phase_ode_solution a ha
  have hcomp := ode_cos_comparison B (fun t => (deriv (phase a (Real.exp a)) t) ^ 2)
    (fun t ht => (hB t ht).1) hBzero hDzero (fun t _ => exp_phase_deriv_sq_mem_Icc a t ha)
    (fun t ht => (hB t ht).2)
  exact ⟨B, hBzero, hDzero, fun t ht => ⟨(hB t ht).1, (hB t ht).2, hcomp t ht⟩⟩

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open Filter Set
open scoped Interval Topology

private theorem local_contDiffAt_deriv {B : ℝ → ℝ} {u : ℝ} {k : WithTop ℕ∞}
    (hB : ContDiffAt ℝ (k + 1) B u) : ContDiffAt ℝ k (deriv B) u := by
  simpa only [deriv] using hB.fderiv_right_succ.clm_apply
    (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ => (1 : ℝ)) u)

private theorem phase_square_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun u => (deriv (phase a (Real.exp a)) u) ^ 2 - 1) := by
  simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' (Real.exp_pos a).ne').deriv]
  fun_prop

/-- An oriented-interval estimate using the weight's regularity near that interval. -/
theorem abs_intervalIntegral_local_weighted_phase
    (a l r : ℝ) (ha : 0 < a) (φ dφ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ u ∈ uIcc l r, HasDerivAt φ (dφ u) u)
    (hdφ : ContinuousOn dφ (uIcc l r)) (hM : ∀ u ∈ uIcc l r, |dφ u| ≤ M) :
    |∫ u in l..r, φ u * ((deriv (phase a (Real.exp a)) u) ^ 2 - 1)| ≤
      (3 / a) * (|φ l| + |φ r| + M * |r - l|) := by
  let P := oscillationPrimitive a (Real.exp a)
  let Q := fun u => (deriv (phase a (Real.exp a)) u) ^ 2 - 1
  have hP (u : ℝ) : HasDerivAt P (Q u) u :=
    oscillationPrimitive_hasDerivAt a (Real.exp a) u ha (two_mul_le_exp_of_nonneg a ha.le)
  have hcontP : ContinuousOn P (uIcc l r) :=
    fun u _ => (hP u).continuousAt.continuousWithinAt
  have hcontφ : ContinuousOn φ (uIcc l r) :=
    fun u hu => (hφ u hu).continuousAt.continuousWithinAt
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcontφ hcontP (fun u hu => hφ u (Ioo_subset_Icc_self hu)) (fun u _ => hP u) hdφ.intervalIntegrable
    ((phase_square_continuous a ha).intervalIntegrable l r)
  have hterm (u z : ℝ) : |z * P u| ≤ (3 / a) * |z| := by
    rw [abs_mul, mul_comm (3 / a)]
    exact mul_le_mul_of_nonneg_left (exp_phase_primitive_bound a u ha) (abs_nonneg z)
  have hInt : |∫ u in l..r, dφ u * P u| ≤ ((3 / a) * M) * |r - l| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := r)
        (C := (3 / a) * M) (f := fun u => dφ u * P u) (fun u hu => by
          rw [Real.norm_eq_abs]
          exact (hterm u (dφ u)).trans
            (mul_le_mul_of_nonneg_left (hM u (uIoc_subset_uIcc hu)) (by positivity))))
  change |∫ u in l..r, φ u * Q u| ≤ _
  rw [hIBP]
  calc
    |φ r * P r - φ l * P l - ∫ u in l..r, dφ u * P u| ≤
        |φ r * P r| + |φ l * P l| + |∫ u in l..r, dφ u * P u| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ (3 / a) * |φ r| + (3 / a) * |φ l| + ((3 / a) * M) * |r - l| :=
      add_le_add (add_le_add (hterm r (φ r)) (hterm l (φ l))) hInt
    _ = _ := by ring

/-- Quantitative control of a Rosen solution and its first derivative. -/
theorem rosen_solution_c1_error (a : ℝ) (ha : 0 < a) (B : ℝ → ℝ)
    (hB : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), ContDiffAt ℝ 2 B u)
    (hBzero : B 0 = 1) (hDzero : deriv B 0 = 0)
    (hODE : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), deriv (deriv B) u =
      -((deriv (phase a (Real.exp a)) u) ^ 2 * B u)) :
    ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      |B t - Real.cos t| ≤ 15 / a ∧ |deriv B t - (-Real.sin t)| ≤ 15 / a := by
  let K := Icc (-(1 / 4) : ℝ) (1 / 4)
  let Q := fun u => (deriv (phase a (Real.exp a)) u) ^ 2 - 1
  let C := fun u => B u * Real.cos u - deriv B u * Real.sin u
  let S := fun u => B u * Real.sin u + deriv B u * Real.cos u
  let φs := fun u => B u * Real.sin u
  let φc := fun u => B u * Real.cos u
  let ds := fun u => deriv B u * Real.sin u + B u * Real.cos u
  let dc := fun u => deriv B u * Real.cos u + B u * (-Real.sin u)
  have hzero : (0 : ℝ) ∈ K := by norm_num [K]
  have hderiv (u : ℝ) (hu : u ∈ K) : ContDiffAt ℝ 1 (deriv B) u :=
    local_contDiffAt_deriv (k := 1) (by
      rw [show (1 : WithTop ℕ∞) + 1 = 2 by norm_num]
      exact hB u hu)
  have hFirst (u : ℝ) (hu : u ∈ K) : HasDerivAt B (deriv B u) u :=
    ((hB u hu).differentiableAt (by norm_num)).hasDerivAt
  have hSecond (u : ℝ) (hu : u ∈ K) : HasDerivAt (deriv B) (deriv (deriv B) u) u :=
    ((hderiv u hu).differentiableAt (by norm_num)).hasDerivAt
  have hCs (u : ℝ) (hu : u ∈ K) : HasDerivAt φs (ds u) u :=
    (hFirst u hu).mul (Real.hasDerivAt_sin u)
  have hCc (u : ℝ) (hu : u ∈ K) : HasDerivAt φc (dc u) u :=
    (hFirst u hu).mul (Real.hasDerivAt_cos u)
  have hC (u : ℝ) (hu : u ∈ K) : HasDerivAt C (φs u * Q u) u := by
    convert ((hFirst u hu).mul (Real.hasDerivAt_cos u)).sub
      ((hSecond u hu).mul (Real.hasDerivAt_sin u)) using 1
    rw [hODE u hu]
    unfold φs Q
    ring
  have hS (u : ℝ) (hu : u ∈ K) : HasDerivAt S (-(φc u * Q u)) u := by
    convert ((hFirst u hu).mul (Real.hasDerivAt_sin u)).add
      ((hSecond u hu).mul (Real.hasDerivAt_cos u)) using 1
    rw [hODE u hu]
    unfold φc Q
    ring
  have hBabs (u : ℝ) (hu : u ∈ K) : |B u| ≤ 1 := by
    have h := ode_cos_comparison B (fun u => (deriv (phase a (Real.exp a)) u) ^ 2)
      hB hBzero hDzero (fun u _ => exp_phase_deriv_sq_mem_Icc a u ha) hODE u hu
    rw [abs_of_pos (h.1.trans_le h.2.1)]
    exact h.2.2.1
  have hDabs (u : ℝ) (hu : u ∈ K) : |deriv B u| ≤ 1 :=
    (ode_cos_comparison B (fun u => (deriv (phase a (Real.exp a)) u) ^ 2)
      hB hBzero hDzero (fun u _ => exp_phase_deriv_sq_mem_Icc a u ha) hODE u hu).2.2.2.1
  have hcontB : ContinuousOn B K := fun u hu => (hB u hu).continuousAt.continuousWithinAt
  have hcontD : ContinuousOn (deriv B) K :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hcontDs : ContinuousOn ds K :=
    (hcontD.mul Real.continuous_sin.continuousOn).add (hcontB.mul Real.continuous_cos.continuousOn)
  have hcontDc : ContinuousOn dc K :=
    (hcontD.mul Real.continuous_cos.continuousOn).add (hcontB.mul Real.continuous_sin.continuousOn.neg)
  have hmul (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφs (u : ℝ) (hu : u ∈ K) : |φs u| ≤ 1 := hmul _ _ (hBabs u hu) (Real.abs_sin_le_one _)
  have hφc (u : ℝ) (hu : u ∈ K) : |φc u| ≤ 1 := hmul _ _ (hBabs u hu) (Real.abs_cos_le_one _)
  have hds (u : ℝ) (hu : u ∈ K) : |ds u| ≤ 2 := by
    refine (abs_add_le _ _).trans ?_
    have h := add_le_add (hmul _ (Real.sin u) (hDabs u hu) (Real.abs_sin_le_one u)) (hφc u hu)
    exact h.trans_eq (by norm_num)
  have hdc (u : ℝ) (hu : u ∈ K) : |dc u| ≤ 2 := by
    refine (abs_add_le _ _).trans ?_
    have h := add_le_add (hmul _ (Real.cos u) (hDabs u hu) (Real.abs_cos_le_one u))
      (hmul _ (-Real.sin u) (hBabs u hu) (by rw [abs_neg]; exact Real.abs_sin_le_one u))
    exact h.trans_eq (by norm_num)
  intro t ht
  have hsub : uIcc 0 t ⊆ K := uIcc_subset_Icc hzero ht
  have htAbs : |t| ≤ 1 / 4 := abs_le.mpr ht
  have hC0 : C 0 = 1 := by simp [C, hBzero]
  have hS0 : S 0 = 0 := by simp [S, hDzero]
  have hQ : Continuous Q := phase_square_continuous a ha
  have hΦs : ContinuousOn φs K := hcontB.mul Real.continuous_sin.continuousOn
  have hΦc : ContinuousOn φc K := hcontB.mul Real.continuous_cos.continuousOn
  have hCFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hC u (hsub hu)) ((hΦs.mul hQ.continuousOn).mono hsub).intervalIntegrable
  have hSFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hS u (hsub hu)) ((hΦc.mul hQ.continuousOn).neg.mono hsub).intervalIntegrable
  have hBound (φ dφ : ℝ → ℝ)
      (hd : ∀ u ∈ K, HasDerivAt φ (dφ u) u) (hc : ContinuousOn dφ K)
      (hφbound : ∀ u ∈ K, |φ u| ≤ 1) (hdφbound : ∀ u ∈ K, |dφ u| ≤ 2) :
      |∫ u in 0..t, φ u * Q u| ≤ 15 / (2 * a) := by
    have h := abs_intervalIntegral_local_weighted_phase a 0 t ha φ dφ 2
      (fun u hu => hd u (hsub hu)) (hc.mono hsub) (fun u hu => hdφbound u (hsub hu))
    change |∫ u in 0..t, φ u * Q u| ≤ _ at h
    calc
      |∫ u in 0..t, φ u * Q u| ≤ (3 / a) * (|φ 0| + |φ t| + 2 * |t - 0|) := h
      _ ≤ (3 / a) * (1 + 1 + 2 * (1 / 4)) := by
        rw [sub_zero]
        exact mul_le_mul_of_nonneg_left (by linarith [hφbound 0 hzero, hφbound t ht, htAbs])
          (by positivity)
      _ = 15 / (2 * a) := by ring
  have hCbound := hBound φs ds hCs hcontDs hφs hds
  rw [hCFTC, hC0] at hCbound
  have hSbound := hBound φc dc hCc hcontDc hφc hdc
  rw [intervalIntegral.integral_neg, hS0, sub_zero] at hSFTC
  have hSbound' : |S t| ≤ 15 / (2 * a) := by rw [← hSFTC, abs_neg]; exact hSbound
  have hBrestore : B t - Real.cos t = (C t - 1) * Real.cos t + S t * Real.sin t := by
    unfold C S
    nlinarith [Real.sin_sq_add_cos_sq t,
      congrArg (fun y : ℝ => B t * y) (Real.sin_sq_add_cos_sq t)]
  have hDrestore : deriv B t - (-Real.sin t) =
      S t * Real.cos t - (C t - 1) * Real.sin t := by
    unfold C S
    nlinarith [Real.sin_sq_add_cos_sq t,
      congrArg (fun y : ℝ => deriv B t * y) (Real.sin_sq_add_cos_sq t)]
  have hterm (x y : ℝ) (hx : |x| ≤ 15 / (2 * a)) (hy : |y| ≤ 1) :
      |x * y| ≤ 15 / (2 * a) := by
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  constructor
  · rw [hBrestore]
    exact ((abs_add_le _ _).trans (add_le_add (hterm _ _ hCbound (Real.abs_cos_le_one _))
      (hterm _ _ hSbound' (Real.abs_sin_le_one _)))).trans_eq (by ring)
  · rw [hDrestore]
    exact ((abs_sub _ _).trans (add_le_add (hterm _ _ hSbound' (Real.abs_cos_le_one _))
      (hterm _ _ hCbound (Real.abs_sin_le_one _)))).trans_eq (by ring)

/-- The actual functions and actual first derivatives converge uniformly on the closed interval. -/
theorem rosen_solution_tendsto_uniformly_c1 (B : ℕ → ℝ → ℝ)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → ContDiffAt ℝ 2 (B n) u)
    (hBzero : ∀ n, B n 0 = 1) (hDzero : ∀ n, deriv (B n) 0 = 0)
    (hODE : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → deriv (deriv (B n)) u =
      -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u) ^ 2 * B n u)) :
    TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
    TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop
      (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
  have hlim : Tendsto (fun n : ℕ => (15 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (15 : ℝ)
  have hest (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :=
    rosen_solution_c1_error ((n : ℝ) + 1) (by positivity) (B n)
      (hB n) (hBzero n) (hDzero n) (hODE n) u hu
  constructor <;> rw [Metric.tendstoUniformlyOn_iff]
  · intro ε hε
    filter_upwards [hlim.eventually_lt_const hε] with n hn u hu
    rw [dist_comm, Real.dist_eq]
    exact (hest n u hu).1.trans_lt hn
  · intro ε hε
    filter_upwards [hlim.eventually_lt_const hε] with n hn u hu
    rw [dist_comm, Real.dist_eq, (Real.hasDerivAt_cos u).deriv]
    exact (hest n u hu).2.trans_lt hn

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open Filter Set

/-- One actual Rosen solution sequence has the stated initial values, pointwise comparison,
    uniform first- and second-derivative bounds, and the full closed-interval first-jet limit. -/
theorem exists_rosen_sequence_c1 :
    ∃ B : ℕ → ℝ → ℝ,
      (∀ n, B n 0 = 1) ∧ (∀ n, deriv (B n) 0 = 0) ∧
      (∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        ContDiffAt ℝ 2 (B n) u ∧
        deriv (deriv (B n)) u =
          -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u) ^ 2 * B n u) ∧
        0 < Real.cos (2 * u) ∧ Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧
        |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4) ∧
      TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop
        (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
  have hEach (n : ℕ) := exists_phase_ode_solution_with_bounds ((n : ℝ) + 1) (by positivity)
  choose B hB0 hD0 hB using hEach
  have hCont (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      ContDiffAt ℝ 2 (B n) u := (hB n u hu).1
  have hODE (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      deriv (deriv (B n)) u =
        -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u) ^ 2 * B n u) :=
    (hB n u hu).2.1
  exact ⟨B, hB0, hD0, hB, rosen_solution_tendsto_uniformly_c1 B hCont hB0 hD0 hODE⟩

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open Filter Set
open scoped ContDiff Topology

/-- A smooth coefficient makes every genuine solution of the first-order system smooth
    on its open domain. The proof bootstraps the ordinary derivative of the pair. -/
theorem ode_pair_contDiffOn_of_hasDerivAt (q : ℝ → ℝ) (state : ℝ → ℝ × ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hstate : ∀ t ∈ U, HasDerivAt state (odeField q t (state t)) t) :
    ContDiffOn ℝ ∞ state U := by
  have hd : DifferentiableOn ℝ state U := fun t ht =>
    (hstate t ht).differentiableAt.differentiableWithinAt
  have heq (t : ℝ) (ht : t ∈ U) : deriv state t = odeField q t (state t) :=
    (hstate t ht).deriv
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hd.continuousOn
  | succ n hn =>
    have hqn : ContDiffOn ℝ (n : WithTop ℕ∞) q U := contDiffOn_infty.mp hq n
    have hfirst : ContDiffOn ℝ (n : WithTop ℕ∞) (fun t => 2 * (state t).2) U :=
      contDiffOn_const.mul hn.snd
    have hsecond : ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun t => -(q t * (state t).1) / 2) U :=
      (hqn.mul hn.fst).neg.div_const 2
    have hfield : ContDiffOn ℝ (n : WithTop ℕ∞) (fun t => odeField q t (state t)) U :=
      hfirst.prodMk hsecond
    rw [Nat.cast_succ]
    exact (contDiffOn_succ_iff_deriv_of_isOpen hU).2 ⟨hd, by simp, hfield.congr heq⟩

/-- The actual Picard solution supplies a smooth scalar solution on an open interval
    strictly containing the closed interval used for comparison and convergence. -/
theorem exists_smooth_scalar_ode_solution (q : ℝ → ℝ) (hqsmooth : ContDiff ℝ ∞ q)
    (hq : ∀ t ∈ Icc (-(1 / 3) : ℝ) (1 / 3), q t ∈ Icc (0 : ℝ) 4) :
    ∃ B : ℝ → ℝ, B 0 = 1 ∧ deriv B 0 = 0 ∧
      ContDiffOn ℝ ∞ B (Ioo (-(1 / 3) : ℝ) (1 / 3)) ∧
      ∀ t ∈ Ioo (-(1 / 3) : ℝ) (1 / 3), deriv (deriv B) t = -(q t * B t) := by
  obtain ⟨state, h0, hstate⟩ := exists_ode_pair q hqsmooth.continuous hq
  let U := Ioo (-(1 / 3) : ℝ) (1 / 3)
  let B := fun t : ℝ => (state t).1
  let V := fun t : ℝ => (state t).2
  have hU : IsOpen U := isOpen_Ioo
  have hactual (t : ℝ) (ht : t ∈ U) : HasDerivAt state (odeField q t (state t)) t :=
    (hstate t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hsmooth := ode_pair_contDiffOn_of_hasDerivAt q state U hU hqsmooth.contDiffOn hactual
  have hderiv (t : ℝ) (ht : t ∈ U) : deriv B t = 2 * V t := by
    have h := (hactual t ht).hasFDerivAt.fst.hasDerivAt.deriv
    simpa [B, V, odeField] using h
  have hODE (t : ℝ) (ht : t ∈ U) : deriv (deriv B) t = -(q t * B t) := by
    have hV : HasDerivAt V (-(q t * B t) / 2) t := by
      simpa [B, V, odeField] using (hactual t ht).hasFDerivAt.snd.hasDerivAt
    have h₂ := hV.const_mul 2
    have heq : 2 * (-(q t * B t) / 2) = -(q t * B t) := by ring
    rw [heq] at h₂
    have hB₂ : HasDerivAt (deriv B) (-(q t * B t)) t := by
      apply h₂.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds ht] with u hu
      exact hderiv u hu
    exact hB₂.deriv
  refine ⟨B, congrArg Prod.fst h0, ?_, hsmooth.fst, hODE⟩
  rw [hderiv 0 (by norm_num [U])]
  change 2 * (state 0).2 = 0
  rw [h0, mul_zero]

/-- The exact two-frequency coefficient is smooth, so the actual scalar solution
    has a smooth open-neighborhood realization without additional inputs. -/
theorem exists_smooth_phase_ode_solution (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ → ℝ, B 0 = 1 ∧ deriv B 0 = 0 ∧
      ContDiffOn ℝ ∞ B (Ioo (-(1 / 3) : ℝ) (1 / 3)) ∧
      ∀ t ∈ Ioo (-(1 / 3) : ℝ) (1 / 3),
        deriv (deriv B) t = -((deriv (phase a (Real.exp a)) t) ^ 2 * B t) := by
  apply exists_smooth_scalar_ode_solution
  · simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' (Real.exp_pos a).ne').deriv]
    fun_prop
  · intro t _
    exact exp_phase_deriv_sq_mem_Icc a t ha

/-- The same smooth two-frequency sequence satisfies the larger-domain equation,
    the closed-interval pointwise estimates, and both uniform first-jet limits. -/
theorem exists_smooth_rosen_sequence_c1 :
    ∃ B : ℕ → ℝ → ℝ,
      (∀ n, B n 0 = 1) ∧ (∀ n, deriv (B n) 0 = 0) ∧
      (∀ n, ContDiffOn ℝ ∞ (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3))) ∧
      (∀ n t, t ∈ Ioo (-(1 / 3) : ℝ) (1 / 3) →
        deriv (deriv (B n)) t =
          -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) t) ^ 2 * B n t)) ∧
      (∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        0 < Real.cos (2 * u) ∧ Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧
        |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4) ∧
      TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop
        (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
  have hEach (n : ℕ) := exists_smooth_phase_ode_solution ((n : ℝ) + 1) (by positivity)
  choose B hB0 hD0 hsmooth hODE using hEach
  have hInterior : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 3) : ℝ) (1 / 3) :=
    fun _ ht => ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
  have hC2 (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      ContDiffAt ℝ 2 (B n) t :=
    (contDiffOn_infty.mp (hsmooth n) 2).contDiffAt (isOpen_Ioo.mem_nhds (hInterior ht))
  have hClosed (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      deriv (deriv (B n)) t =
        -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) t) ^ 2 * B n t) :=
    hODE n t (hInterior ht)
  refine ⟨B, hB0, hD0, hsmooth, ?_, ?_, rosen_solution_tendsto_uniformly_c1 B hC2 hB0 hD0 hClosed⟩
  · intro n t ht
    exact hODE n t ht
  · intro n t ht
    exact ode_cos_comparison (B n)
      (fun u => (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u) ^ 2)
      (hC2 n) (hB0 n) (hD0 n)
      (fun u _ => exp_phase_deriv_sq_mem_Icc ((n : ℝ) + 1) u (by positivity)) (hClosed n) t ht

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

private abbrev rosenOpenInterval : Set ℝ := Ioo (-(1 / 4) : ℝ) (1 / 4)

private abbrev rosenIntervalVolume : Measure ℝ := volume.restrict rosenOpenInterval

private theorem rosenIntervalVolume_real_univ :
    rosenIntervalVolume.real Set.univ = (1 / 2 : ℝ) := by
  rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4 - -(1 / 4))]
  norm_num

/-- Every actual integrable test on the open Rosen interval admits smooth approximations
    in the norm given by the actual integral of its absolute error. -/
theorem exists_smooth_L1_approx_rosen_interval (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo (-(1 / 4) : ℝ) (1 / 4))) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ IntegrableOn g (Ioo (-(1 / 4) : ℝ) (1 / 4)) ∧
      (∫ u in Ioo (-(1 / 4) : ℝ) (1 / 4), |f u - g u|) ≤ ε := by
  let μ := rosenIntervalVolume
  let f₀ := rosenOpenInterval.indicator f
  have hf₀ : Integrable f₀ (volume : Measure ℝ) := hf.integrable_indicator measurableSet_Ioo
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨g₀, hcompact, hApprox₀, hcontinuous, hg₀⟩ :=
    hf₀.exists_hasCompactSupport_integral_sub_le hδ
  have hApprox : (∫ u, |f u - g₀ u| ∂μ) ≤ ε / 2 := by
    have heq : (fun u => |f u - g₀ u|) =ᵐ[μ] (fun u => |f₀ u - g₀ u|) := by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with u hu
      simp only [f₀, indicator_of_mem hu]
    rw [integral_congr_ae heq]
    have hfg : Integrable (fun u => |f₀ u - g₀ u|) (volume : Measure ℝ) :=
      (hf₀.sub hg₀).abs
    exact (setIntegral_le_integral hfg (Eventually.of_forall fun _ => abs_nonneg _)).trans
      (by simpa only [Real.norm_eq_abs] using hApprox₀)
  obtain ⟨g, hsmooth, hclose⟩ :=
    (hcompact.uniformContinuous_of_continuous hcontinuous).exists_contDiff_dist_le hδ
  have hg : Integrable g μ := hsmooth.continuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hg₀' : Integrable g₀ μ := hg₀.mono_measure Measure.restrict_le_self
  have hf' : Integrable f μ := hf
  have hDifference : (∫ u, |g₀ u - g u| ∂μ) ≤ ε / 4 := by
    letI : IsFiniteMeasure μ := by dsimp [μ, rosenIntervalVolume, rosenOpenInterval]; infer_instance
    have hpoint (u : ℝ) : |g₀ u - g u| ≤ ε / 2 := by
      have h := (hclose u).le
      simpa only [Real.dist_eq, abs_sub_comm] using h
    have hupper : (∫ u, |g₀ u - g u| ∂μ) ≤ ∫ _ : ℝ, ε / 2 ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const _) (Eventually.of_forall hpoint)
    rw [integral_const] at hupper
    change _ ≤ rosenIntervalVolume.real Set.univ • (ε / 2) at hupper
    rw [rosenIntervalVolume_real_univ, smul_eq_mul] at hupper
    exact hupper.trans_eq (by ring)
  have hsum : (∫ u, |f u - g u| ∂μ) ≤ (∫ u, |f u - g₀ u| ∂μ) + ∫ u, |g₀ u - g u| ∂μ := by
    have hf₀diff : Integrable (fun u => |f u - g₀ u|) μ := (hf'.sub hg₀').abs
    have hg₀diff : Integrable (fun u => |g₀ u - g u|) μ := (hg₀'.sub hg).abs
    rw [← integral_add hf₀diff hg₀diff]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hf₀diff.add hg₀diff)
    exact Eventually.of_forall (fun u => abs_sub_le (f u) (g₀ u) (g u))
  refine ⟨g, hsmooth, hg, ?_⟩
  exact hsum.trans (by linarith)

private theorem centered_phase_test_integrable (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (hf : Integrable f rosenIntervalVolume) :
    Integrable (fun u => f u * ((deriv (phase a (Real.exp a)) u)^2 - 1)) rosenIntervalVolume := by
  have hcont : Continuous (fun u => (deriv (phase a (Real.exp a)) u)^2 - 1) := by
    simp_rw [(phase_hasDerivAt a (Real.exp a) _ ha.ne' (Real.exp_pos a).ne').deriv]
    fun_prop
  have hbound : ∃ C : ℝ, ∀ u, ‖(deriv (phase a (Real.exp a)) u)^2 - 1‖ ≤ C := by
    refine ⟨3, fun u => ?_⟩
    have ⟨hlo, hhi⟩ := exp_phase_deriv_sq_mem_Icc a u ha
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [mul_comm] using hf.bdd_mul hcont.aestronglyMeasurable hbound

private theorem centered_phase_test_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (hf : Integrable f rosenIntervalVolume) :
    |∫ u, f u * ((deriv (phase a (Real.exp a)) u)^2 - 1) ∂rosenIntervalVolume| ≤
      3 * ∫ u, |f u| ∂rosenIntervalVolume := by
  rw [← integral_const_mul]
  simp only [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul 3)
  refine Eventually.of_forall fun u => ?_
  rw [norm_mul, mul_comm 3]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have ⟨hlo, hhi⟩ := exp_phase_deriv_sq_mem_Icc a u ha
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Centered two-frequency coefficients tend to zero against every fixed real L¹ test
    with respect to actual Lebesgue measure restricted to the open Rosen interval. -/
theorem tendsto_rosen_centered_phase_all_L1 (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo (-(1 / 4) : ℝ) (1 / 4))) :
    Tendsto (fun n : ℕ => ∫ u in Ioo (-(1 / 4) : ℝ) (1 / 4),
      f u * ((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2 - 1)) atTop (𝓝 0) := by
  let l : ℝ := -(1 / 4)
  let r : ℝ := 1 / 4
  let μ := rosenIntervalVolume
  let Q := fun n : ℕ => fun u : ℝ =>
    (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2 - 1
  have hle : l ≤ r := by norm_num [l, r]
  have hf' : Integrable f μ := hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hgSmooth, hg, hApprox⟩ := exists_smooth_L1_approx_rosen_interval f hf
    (show 0 < ε / 12 by positivity)
  have hg' : Integrable g μ := hg
  have hg1 : ContDiff ℝ 1 g := (contDiff_infty.mp hgSmooth) 1
  let C := |g r| + |g l| + ∫ u in l..r, |deriv g u|
  have hSmooth := tendsto_weighted_phase_deriv_sq_sub_one l r hle (fun _ => g)
    (fun _ => hg1) C (fun _ => le_rfl)
  have hSmoothSet : Tendsto (fun n : ℕ => ∫ u, g u * Q n u ∂μ) atTop (𝓝 0) := by
    have hIntegral (n : ℕ) : (∫ u in l..r, g u * Q n u) = ∫ u, g u * Q n u ∂μ := by
      rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
    exact hSmooth.congr' (Eventually.of_forall hIntegral)
  have hHalf : 0 < ε / 2 := by positivity
  filter_upwards [(Metric.tendsto_nhds.mp hSmoothSet) (ε / 2) hHalf] with n hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hfi : Integrable (fun u => f u * Q n u) μ := centered_phase_test_integrable _ hpos f hf'
  have hgi : Integrable (fun u => g u * Q n u) μ := centered_phase_test_integrable _ hpos g hg'
  have hSplit : (∫ u, f u * Q n u ∂μ) - ∫ u, g u * Q n u ∂μ =
      ∫ u, (f u - g u) * Q n u ∂μ := by
    rw [← integral_sub hfi hgi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => (sub_mul _ _ _).symm)
  rw [Real.dist_eq, sub_zero] at hn ⊢
  change |∫ u, f u * Q n u ∂μ| < ε
  have hBound : |∫ u, (f u - g u) * Q n u ∂μ| ≤ 3 * (ε / 12) :=
    (centered_phase_test_bound _ hpos (f - g) (hf'.sub hg')).trans
      (mul_le_mul_of_nonneg_left hApprox (by norm_num))
  have hTri := abs_add_le ((∫ u, f u * Q n u ∂μ) - ∫ u, g u * Q n u ∂μ)
    (∫ u, g u * Q n u ∂μ)
  rw [sub_add_cancel, hSplit] at hTri
  linarith

/-- Weak-* convergence of the actual squared phase derivatives to one, with a uniform
    actual essential-supremum bound and integrability of every tested product. -/
theorem rosen_phase_LInfinity_weakStar :
    (∀ n : ℕ, eLpNorm (fun u =>
      (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2) ∞
      (volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4))) ≤ ENNReal.ofReal 4) ∧
    ∀ f : ℝ → ℝ, IntegrableOn f (Ioo (-(1 / 4) : ℝ) (1 / 4)) →
      (∀ n : ℕ, IntegrableOn (fun u => f u *
        (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2)
        (Ioo (-(1 / 4) : ℝ) (1 / 4))) ∧
      Tendsto (fun n : ℕ => ∫ u in Ioo (-(1 / 4) : ℝ) (1 / 4),
        f u * (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2) atTop
        (𝓝 (∫ u in Ioo (-(1 / 4) : ℝ) (1 / 4), f u)) := by
  let μ := rosenIntervalVolume
  let q := fun n : ℕ => fun u : ℝ => (deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) u)^2
  have hq (n : ℕ) (u : ℝ) : q n u ∈ Icc (0 : ℝ) 4 :=
    exp_phase_deriv_sq_mem_Icc ((n : ℝ) + 1) u (by positivity)
  constructor
  · intro n
    change eLpNorm (q n) ∞ μ ≤ ENNReal.ofReal 4
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq n u).1]
      exact (hq n u).2)
  · intro f hf
    have hf' : Integrable f μ := hf
    have hfi (n : ℕ) : Integrable (fun u => f u * (q n u - 1)) μ :=
      centered_phase_test_integrable ((n : ℝ) + 1) (by positivity) f hf'
    have hprod (n : ℕ) : Integrable (fun u => f u * q n u) μ := by
      apply (hfi n).add hf' |>.congr
      exact Eventually.of_forall (fun u => by dsimp; ring)
    refine ⟨hprod, ?_⟩
    have hlim : Tendsto (fun n : ℕ => ∫ u, f u * (q n u - 1) ∂μ) atTop (𝓝 0) :=
      tendsto_rosen_centered_phase_all_L1 f hf
    have hEq (n : ℕ) : (∫ u, f u * (q n u - 1) ∂μ) + ∫ u, f u ∂μ =
        ∫ u, f u * q n u ∂μ := by
      rw [← integral_add (hfi n) hf']
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by dsimp; ring)
    simpa only [hEq, zero_add] using hlim.add (tendsto_const_nhds (x := ∫ u, f u ∂μ))

end Burnett.RosenMultiscale
