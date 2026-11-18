import Burnett.Counterexamples.Rosen.Phase
import Burnett.Counterexamples.Rosen.Coordinates
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rosen multiscale example

Convergence, first derivatives, and the obstruction to a common scale.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenMultiscale

open Set Filter
open scoped ContDiff Topology

theorem exists_smooth_rosen_sequence_c1_and_zero_source :
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
        (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      ∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        let ψ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
        let J := coordinateJacobian (rosenCoordinates (B n)) point
        (J.transpose * originalRosenField (B n) ψ (rosenCoordinates (B n) point) * J =
          pulledRosenField (B n) ψ point) ∧
        ∀ i, contractedSource (B n) ψ point i = 0 := by
  obtain ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim'⟩ := exists_smooth_rosen_sequence_c1
  refine ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim', ?_⟩
  intro n point ht
  have hi : point 0 ∈ Ioo (-(1 / 3) : ℝ) (1 / 3) :=
    ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
  have hd : DifferentiableAt ℝ (B n) (point 0) :=
    ((contDiffOn_infty.mp (hs n) 1).contDiffAt (isOpen_Ioo.mem_nhds hi)).differentiableAt (by norm_num)
  have bounds := hbounds n (point 0) ht
  exact rosen_coordinate_pullback_source_zero _ _ _ hd (bounds.1.trans_le bounds.2.1)

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set

theorem cos_half_le_cos_double (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    Real.cos (1 / 2) ≤ Real.cos (2 * u) := by
  have habs : |2 * u| ≤ (1 / 2 : ℝ) := (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hπ : (1 / 2 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2 * u)) hπ habs
  rwa [Real.cos_abs] at h

theorem screen_component_dist_lower (a b limit ψ : ℝ) (ha : 0 < a)
    (hb : Real.cos (1 / 2) ≤ b) (hψ : 1 / (2 * a) ≤ ψ) :
    (Real.cos (1 / 2))^2 / (2 * a) ≤
      max |screenX b ψ - limit| |screenZ b ψ - limit| := by
  have hcos : 0 < Real.cos (1 / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hβ : 0 < b := hcos.trans_le hb
  have hb2 : (Real.cos (1 / 2))^2 ≤ b^2 := by nlinarith
  have ha2 : 0 < 2 * a := by positivity
  have hpositive : 0 ≤ ψ := (one_div_nonneg.mpr ha2.le).trans hψ
  have he := Real.add_one_le_exp (2 * ψ)
  have heminus : Real.exp (-2 * ψ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hgrowth : 1 / a ≤ Real.exp (2 * ψ) - Real.exp (-2 * ψ) := by
    have hid : 2 * (1 / (2 * a)) = 1 / a := by ring
    rw [← hid]
    linarith
  let X := screenX b ψ - limit
  let Z := screenZ b ψ - limit
  have hupper : X - Z ≤ 2 * max |X| |Z| := by
    have hx := le_abs_self X
    have hz := neg_le_abs Z
    linarith [le_max_left |X| |Z|, le_max_right |X| |Z|]
  have hlower : (Real.cos (1 / 2))^2 * (1 / a) ≤ X - Z := by
    calc
      (Real.cos (1 / 2))^2 * (1 / a) ≤ b^2 * (1 / a) :=
        mul_le_mul_of_nonneg_right hb2 (by positivity)
      _ ≤ b^2 * (Real.exp (2 * ψ) - Real.exp (-2 * ψ)) :=
        mul_le_mul_of_nonneg_left hgrowth (sq_nonneg _)
      _ = X - Z := by simp only [X, Z, screenX, screenZ]; ring
  have hidentity : (Real.cos (1 / 2))^2 * (1 / a) = 2 * ((Real.cos (1 / 2))^2 / (2 * a)) := by ring
  rw [hidentity] at hlower
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp
    (by simpa only [mul_comm (2 : ℝ)] using hlower.trans hupper)

theorem rosen_metric_amplitude_lower_at_peak (a : ℝ) (ha : 0 < a) (B : ℝ → ℝ)
    (hcos : ∀ u ∈ Icc (-(1 / 4) : ℝ) (1 / 4), Real.cos (2 * u) ≤ B u)
    (hu : Real.pi / (2 * a) ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let u := Real.pi / (2 * a)
    let ψ := phase a (Real.exp a) u
    (Real.cos (1 / 2))^2 / (2 * a) ≤
      max |screenX (B u) ψ - (Real.cos u)^2| |screenZ (B u) ψ - (Real.cos u)^2| :=
  screen_component_dist_lower a _ _ _ ha ((cos_half_le_cos_double _ hu).trans (hcos _ hu))
    (exp_phase_peak_bounds a ha).1

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set Filter
open scoped Topology

theorem screenX_second_deriv (B ψ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hB : ContDiffOn ℝ 2 B U) (hψ : ContDiffOn ℝ 2 ψ U) (u : ℝ) (hu : u ∈ U) :
    deriv (deriv (fun t => screenX (B t) (ψ t))) u =
      Real.exp (2 * ψ u) *
        (2 * (B u)^2 * deriv (deriv ψ) u + 2 * (deriv B u)^2 +
          2 * B u * deriv (deriv B) u + 8 * B u * deriv B u * deriv ψ u +
          4 * (B u)^2 * (deriv ψ u)^2) := by
  have hBd (t : ℝ) (ht : t ∈ U) := ((hB.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  have hψd (t : ℝ) (ht : t ∈ U) := ((hψ.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  have hBderiv : ContDiffOn ℝ 1 (deriv B) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).mp hB).2.2
  have hψderiv : ContDiffOn ℝ 1 (deriv ψ) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).mp hψ).2.2
  have hBdd := ((hBderiv.contDiffAt (hU.mem_nhds hu)).differentiableAt (by norm_num)).hasDerivAt
  have hψdd := ((hψderiv.contDiffAt (hU.mem_nhds hu)).differentiableAt (by norm_num)).hasDerivAt
  let E := fun t => Real.exp (2 * ψ t)
  let D := fun t => 2 * B t * deriv B t + (B t)^2 * (2 * deriv ψ t)
  have hEd (t : ℝ) (ht : t ∈ U) : HasDerivAt E (Real.exp (2 * ψ t) * (2 * deriv ψ t)) t :=
    ((hψd t ht).const_mul 2).exp
  have hfirst (t : ℝ) (ht : t ∈ U) :
      deriv (fun v => screenX (B v) (ψ v)) t = E t * D t := by
    have hd := ((hBd t ht).pow 2).mul (hEd t ht)
    change deriv (B ^ 2 * E) t = E t * D t
    rw [hd.deriv]
    simp only [Pi.pow_apply, Nat.reduceSub, pow_one]
    unfold D E
    ring
  have hD := (((hBd u hu).const_mul 2).mul hBdd).add
    (((hBd u hu).pow 2).mul (hψdd.const_mul 2))
  have hDE := (hEd u hu).mul hD
  have hactual : (deriv fun t => screenX (B t) (ψ t)) =ᶠ[𝓝 u] fun t => E t * D t := by
    filter_upwards [hU.mem_nhds hu] with t ht
    exact hfirst t ht
  rw [hactual.deriv_eq]
  change deriv (E * ((fun t => 2 * B t) * deriv B + B ^ 2 * fun t => 2 * deriv ψ t)) u = _
  rw [hDE.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Nat.reduceSub, pow_one]
  unfold E
  ring

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set Filter

theorem abs_exp_phase_le_two (a u : ℝ) (ha : 1 ≤ a) :
    |phase a (Real.exp a) u| ≤ 2 := by
  have ha0 : 0 < a := by linarith
  have he : 1 ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have h₁ : |scaledSine a u| ≤ 1 := (abs_scaledSine_le _ _).trans (by
    rw [abs_of_pos ha0]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ha)
  have h₂ : |scaledSine (Real.exp a) u| ≤ 1 := (abs_scaledSine_le _ _).trans (by
    rw [abs_of_pos (Real.exp_pos a)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) he)
  exact (abs_add_le _ _).trans (by linarith)

theorem abs_exp_phase_deriv_le_two (a u : ℝ) (ha : 0 < a) :
    |deriv (phase a (Real.exp a)) u| ≤ 2 := by
  rw [(phase_hasDerivAt a (Real.exp a) u ha.ne' (Real.exp_pos a).ne').deriv]
  exact (abs_add_le _ _).trans (by
    linarith [Real.abs_cos_le_one (a * u), Real.abs_cos_le_one (Real.exp a * u)])

theorem screenX_derivative_remainder_bound (b b1 b2 p1 : ℝ)
    (hb : |b| ≤ 1) (hb1 : |b1| ≤ 1) (hb2 : |b2| ≤ 4) (hp1 : |p1| ≤ 2) :
    |2 * b1^2 + 2 * b * b2 + 8 * b * b1 * p1 + 4 * b^2 * p1^2| ≤ 42 := by
  have hbb : b^2 ≤ 1 := by
    have h := mul_le_mul hb hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [sq_abs b]
  have h11 : b1^2 ≤ 1 := by
    have h := mul_le_mul hb1 hb1 (abs_nonneg b1) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [sq_abs b1]
  have hpp : p1^2 ≤ 4 := by
    have h := mul_le_mul hp1 hp1 (abs_nonneg p1) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [sq_abs p1]
  have hA : |2 * b1^2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hB : |2 * b * b2| ≤ 8 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h0 : 2 * |b| ≤ 2 := by linarith
    calc
      (2 : ℝ) * |b| * |b2| ≤ 2 * 4 := mul_le_mul h0 hb2 (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hC : |8 * b * b1 * p1| ≤ 16 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    have h0 : 8 * |b| ≤ 8 := by linarith
    have h12 : 8 * |b| * |b1| ≤ 8 * 1 := mul_le_mul h0 hb1 (abs_nonneg _) (by norm_num)
    calc
      (8 : ℝ) * |b| * |b1| * |p1| ≤ (8 * 1) * 2 :=
        mul_le_mul h12 hp1 (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hD : |4 * b^2 * p1^2| ≤ 16 := by
    rw [abs_of_nonneg (by positivity)]
    have h0 : 4 * b^2 ≤ 4 := by linarith
    calc
      (4 : ℝ) * b^2 * p1^2 ≤ 4 * 4 := mul_le_mul h0 hpp (sq_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hsum := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hA hB)) hC)) hD)
  norm_num at hsum ⊢
  exact hsum

theorem screenX_derivative_lower_of_bounds (b b1 b2 p p1 p2 : ℝ)
    (hbc : Real.cos (1 / 2) ≤ b) (hb : |b| ≤ 1)
    (hb1 : |b1| ≤ 1) (hb2 : |b2| ≤ 4) (hp : |p| ≤ 2) (hp1 : |p1| ≤ 2) :
    2 * Real.exp (-4) * (Real.cos (1 / 2))^2 * |p2| - 42 * Real.exp 4 ≤
    |Real.exp (2 * p) * (2 * b^2 * p2 + 2 * b1^2 + 2 * b * b2 + 8 * b * b1 * p1 + 4 * b^2 * p1^2)| := by
  let R := 2 * b1^2 + 2 * b * b2 + 8 * b * b1 * p1 + 4 * b^2 * p1^2
  have hr : |R| ≤ 42 := screenX_derivative_remainder_bound b b1 b2 p1 hb hb1 hb2 hp1
  have hcos : 0 < Real.cos (1/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hb2lo : (Real.cos (1/2))^2 ≤ b^2 := by nlinarith
  have heL : Real.exp (-4) ≤ Real.exp (2 * p) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hp).1])
  have heU : Real.exp (2 * p) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hp).2])
  have he : 0 ≤ Real.exp (2 * p) := (Real.exp_pos _).le
  have coeff : 2 * Real.exp (-4) * (Real.cos (1/2))^2 ≤ Real.exp (2 * p) * (2 * b^2) := by
    have hmul := mul_le_mul heL hb2lo (sq_nonneg (Real.cos (1/2))) he
    calc
      2 * Real.exp (-4) * (Real.cos (1/2))^2 = 2 * (Real.exp (-4) * (Real.cos (1/2))^2) := by ring
      _ ≤ 2 * (Real.exp (2 * p) * b^2) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by ring
  have eta : 2 * b^2 * p2 = (2 * b^2 * p2 + R) - R := by ring
  have htriangle : 2 * b^2 * |p2| ≤ |2 * b^2 * p2 + R| + |R| := by
    calc
      2 * b^2 * |p2| = |(2 * b^2) * p2| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * b^2)]
      _ = |(2 * b^2 * p2 + R) - R| := congrArg abs eta
      _ ≤ _ := abs_sub _ _
  have hErr : Real.exp (2 * p) * |R| ≤ 42 * Real.exp 4 := by
    have ht := mul_le_mul heU hr (abs_nonneg _) (Real.exp_pos _).le
    simpa only [mul_comm (Real.exp 4) 42] using ht
  have hgoal : 2 * Real.exp (-4) * (Real.cos (1/2))^2 * |p2| ≤
      |Real.exp (2 * p) * (2 * b^2 * p2 + R)| + 42 * Real.exp 4 := by
    calc
      2 * Real.exp (-4) * (Real.cos (1/2))^2 * |p2| ≤ (Real.exp (2 * p) * (2 * b^2)) * |p2| :=
        mul_le_mul_of_nonneg_right coeff (abs_nonneg _)
      _ = Real.exp (2 * p) * (2 * b^2 * |p2|) := by ring
      _ ≤ Real.exp (2 * p) * (|2 * b^2 * p2 + R| + |R|) := mul_le_mul_of_nonneg_left htriangle he
      _ = |Real.exp (2 * p) * (2 * b^2 * p2 + R)| + Real.exp (2 * p) * |R| := by
        rw [abs_mul, abs_of_nonneg he]
        ring
      _ ≤ _ := add_le_add_left hErr _
  have hsum : 2 * b^2 * p2 + R = 2 * b^2 * p2 + 2 * b1^2 + 2 * b * b2 + 8 * b * b1 * p1 + 4 * b^2 * p1^2 := by
    unfold R
    ring
  rw [hsum] at hgoal
  exact sub_le_iff_le_add.mpr hgoal

theorem rosen_metric_hessian_lower_at_fast_peak (a : ℝ) (ha : 1 ≤ a) (B : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U)
    (hJ : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ U)
    (hb : ∀ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
      Real.cos (2 * t) ≤ B t ∧ B t ≤ 1 ∧ |deriv B t| ≤ 1 ∧ |deriv (deriv B) t| ≤ 4)
    (hu : Real.pi / (2 * Real.exp a) ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let u := Real.pi / (2 * Real.exp a)
    let ψ := phase a (Real.exp a)
    2 * Real.exp (-4) * (Real.cos (1/2))^2 * Real.exp a - 42 * Real.exp 4 ≤
      |deriv (deriv (fun t => screenX (B t) (ψ t))) u| := by
  let u := Real.pi / (2 * Real.exp a)
  let ψ := phase a (Real.exp a)
  have ha0 : 0 < a := by linarith
  have hψ : ContDiff ℝ 2 ψ := by
    unfold ψ phase scaledSine
    fun_prop
  have hcos : Real.cos (1/2) ≤ B u := (cos_half_le_cos_double u hu).trans (hb u hu).1
  have hcospos : 0 < Real.cos (1/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hbabs : |B u| ≤ 1 := by
    rw [abs_of_pos (hcospos.trans_le hcos)]
    exact (hb u hu).2.1
  have hx := screenX_derivative_lower_of_bounds (B u) (deriv B u) (deriv (deriv B) u)
    (ψ u) (deriv ψ u) (deriv (deriv ψ) u) hcos hbabs (hb u hu).2.2.1 (hb u hu).2.2.2
    (abs_exp_phase_le_two a u ha) (abs_exp_phase_deriv_le_two a u ha0)
  have hy : 2 * Real.exp (-4) * (Real.cos (1/2))^2 * Real.exp a - 42 * Real.exp 4 ≤
      2 * Real.exp (-4) * (Real.cos (1/2))^2 * |deriv (deriv ψ) u| - 42 * Real.exp 4 :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left (exp_phase_peak_bounds a ha0).2 (by positivity)) _
  change _ ≤ |deriv (deriv (fun t => screenX (B t) (ψ t))) u|
  rw [screenX_second_deriv B ψ U hU hB hψ.contDiffOn u (hJ hu)]
  exact hy.trans hx

end Burnett.RosenMultiscale

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Filter

theorem no_common_scale_of_separated_growth (c d K : ℝ) (hc : 0 < c) (hd : 0 < d) :
    ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, ∀ᶠ n in atTop,
      0 < δ n ∧ c / ((n : ℝ) + 1) ≤ δ n ∧
        d * Real.exp ((n : ℝ) + 1) - K ≤ C / δ n := by
  rintro ⟨δ, C, hδ⟩
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hn
  have hratio : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop atTop := by
    simpa only [Function.comp_def, pow_one] using (Real.tendsto_exp_div_pow_atTop 1).comp hn
  have hdc : 0 < d * c / 2 := by positivity
  obtain ⟨n, ⟨hnδ, hLower, hUpper⟩, hExp, hRatio⟩ :=
    (hδ.and ((hexp.eventually_ge_atTop (2 * K / d)).and
      (hratio.eventually_ge_atTop ((C + 1) / (d * c / 2))))).exists
  let a := (n : ℝ) + 1
  have hlarge : K ≤ d * Real.exp a / 2 := by
    have := (div_le_iff₀ hd).mp hExp
    dsimp [a]
    linarith
  have hcoeff : 0 < d * Real.exp a / 2 := by positivity
  have hUpper' : (d * Real.exp a / 2) * δ n ≤ C := by
    apply (le_div_iff₀ hnδ).mp
    change d * Real.exp a / 2 ≤ C / δ n
    exact (by linarith : d * Real.exp a / 2 ≤ d * Real.exp a - K).trans hUpper
  have hLargeRatio : C + 1 ≤ (Real.exp a / a) * (d * c / 2) := (div_le_iff₀ hdc).mp hRatio
  have hSmallRatio : (Real.exp a / a) * (d * c / 2) ≤ C := by
    calc
      (Real.exp a / a) * (d * c / 2) = (d * Real.exp a / 2) * (c / a) := by ring
      _ ≤ (d * Real.exp a / 2) * δ n := mul_le_mul_of_nonneg_left hLower hcoeff.le
      _ ≤ C := hUpper'
  linarith


end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set Filter
open scoped Topology

theorem rosen_sampling_points_eventually_mem (left right : ℝ) (hl : left < 0) (hr : 0 < right) :
    ∀ᶠ n : ℕ in atTop,
      Real.pi / (2 * ((n : ℝ) + 1)) ∈ Icc left right ∧
      Real.pi / (2 * Real.exp ((n : ℝ) + 1)) ∈ Icc left right := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 1)) atTop atTop := Real.tendsto_exp_atTop.comp hn
  have hs : Tendsto (fun n : ℕ => Real.pi / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hf : Tendsto (fun n : ℕ => Real.pi / (2 * Real.exp ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (he.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  exact (hs.eventually_mem (Icc_mem_nhds hl hr)).and (hf.eventually_mem (Icc_mem_nhds hl hr))

theorem rosen_no_common_metric_scale (B : ℕ → ℝ → ℝ)
    (hB : ∀ n, ContDiffOn ℝ 2 (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3)))
    (hb : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧ |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4)
    (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hsub : Icc left right ⊆ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, ∀ᶠ n in atTop,
      0 < δ n ∧
      ∀ u ∈ Icc left right,
        max |screenX (B n u) (ψ n u) - (Real.cos u)^2|
            |screenZ (B n u) (ψ n u) - (Real.cos u)^2| ≤ δ n ∧
        |deriv (deriv (fun t => screenX (B n t) (ψ n t))) u| ≤ C / δ n := by
  dsimp only
  rintro ⟨δ, C, hcontrols⟩
  have hcos : 0 < Real.cos (1/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hcover : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 3) : ℝ) (1 / 3) :=
    fun _ ht => ⟨lt_of_lt_of_le (by norm_num) ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
  apply no_common_scale_of_separated_growth ((Real.cos (1/2))^2 / 2)
    (2 * Real.exp (-4) * (Real.cos (1/2))^2) (42 * Real.exp 4) (by positivity) (by positivity)
  refine ⟨δ, C, ?_⟩
  filter_upwards [hcontrols, rosen_sampling_points_eventually_mem left right hl hr] with n hc hp
  obtain ⟨hs, hf⟩ := hp
  let a := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hm := (rosen_metric_amplitude_lower_at_peak a ha (B n) (fun t ht => (hb n t ht).1) (hsub hs)).trans
    (hc.2 _ hs).1
  have hh := (rosen_metric_hessian_lower_at_fast_peak a ha1 (B n) _ isOpen_Ioo (hB n) hcover (hb n)
    (hsub hf)).trans (hc.2 _ hf).2
  refine ⟨hc.1, ?_, hh⟩
  have hrewrite : ((Real.cos (1/2))^2 / 2) / a = (Real.cos (1/2))^2 / (2 * a) := by ring
  change ((Real.cos (1/2))^2 / 2) / a ≤ δ n
  rwa [hrewrite]

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set

def rosenScaleBox (left right : ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi univ (fun i => if i = 0 then Icc left right else Icc (-1) 1)

theorem rosenScaleBox_subset_closure_interior (left right : ℝ) (hlt : left < right) :
    rosenScaleBox left right ⊆ closure (interior (rosenScaleBox left right)) := by
  let inside : Set (Fin 4 → ℝ) := Set.pi univ (fun i => if i = 0 then Ioo left right else Ioo (-1) 1)
  have hopen : IsOpen inside := isOpen_set_pi finite_univ (fun i _ => by
    split <;> exact isOpen_Ioo)
  have hsub : inside ⊆ rosenScaleBox left right := by
    intro point hp i hi
    have h := hp i hi
    by_cases h0 : i = 0
    · have h' : point i ∈ Ioo left right := by simpa [h0] using h
      simpa [h0] using (show point i ∈ Icc left right from ⟨h'.1.le, h'.2.le⟩)
    · have h' : point i ∈ Ioo (-1 : ℝ) 1 := by simpa [h0] using h
      simpa [h0] using (show point i ∈ Icc (-1 : ℝ) 1 from ⟨h'.1.le, h'.2.le⟩)
  have hclose : closure inside = rosenScaleBox left right := by
    unfold inside rosenScaleBox
    rw [closure_pi_set]
    apply Set.pi_congr rfl
    intro i _
    split_ifs
    · exact closure_Ioo hlt.ne
    · exact closure_Ioo (by norm_num)
  calc
    rosenScaleBox left right = closure inside := hclose.symm
    _ ⊆ closure (interior (rosenScaleBox left right)) := closure_mono (hopen.subset_interior_iff.mpr hsub)

theorem rosenScaleBox_pointwise_of_essential_bound (left right : ℝ) (hlt : left < right)
    (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f (rosenScaleBox left right))
    (C : ℝ) (hC : 0 ≤ C)
    (h : eLpNormEssSup f (volume.restrict (rosenScaleBox left right)) ≤ ENNReal.ofReal C) :
    ∀ point ∈ rosenScaleBox left right, |f point| ≤ C := by
  have habs : ∀ᵐ point ∂(volume.restrict (rosenScaleBox left right)), |f point| ≤ C := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f (volume.restrict (rosenScaleBox left right))] with point hp
    have := hp.trans h
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hC] at this
    exact this
  have heq : (fun point => max |f point| C) =ᵐ[volume.restrict (rosenScaleBox left right)]
      (fun _ => C) := habs.mono (fun _ hp => max_eq_right hp)
  have hmax : ContinuousOn (fun point => max |f point| C) (rosenScaleBox left right) :=
    hf.abs.sup continuousOn_const
  have hp := Measure.eqOn_of_ae_eq heq hmax continuousOn_const
    (rosenScaleBox_subset_closure_interior left right hlt)
  intro point hpoint
  exact (le_max_left |f point| C).trans (hp hpoint).le

def rosenMetricInCoordinates (pulled : Bool) (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) : CoordinateMetric :=
  if pulled then pulledRosenField B ψ point else originalRosenField B ψ point

theorem rosenMetricInCoordinates_xx (pulled : Bool) (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) :
    rosenMetricInCoordinates pulled B ψ point 2 2 = screenX (B (point 0)) (ψ (point 0)) := by
  cases pulled <;> rfl

theorem rosenMetricInCoordinates_zz (pulled : Bool) (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) :
    rosenMetricInCoordinates pulled B ψ point 3 3 = screenZ (B (point 0)) (ψ (point 0)) := by
  cases pulled <;> rfl

theorem rosen_no_common_essential_metric_scale (B : ℕ → ℝ → ℝ)
    (hB : ∀ n, ContDiffOn ℝ 2 (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3)))
    (hb : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧ |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4)
    (pulled : Bool) (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hsub : Icc left right ⊆ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let F := rosenMetricInCoordinates pulled
    let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    let μ := volume.restrict (rosenScaleBox left right)
    ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      0 < δ n ∧
      eLpNormEssSup (fun point =>
        max |F (B n) (ψ n) point 2 2 - F Real.cos (fun _ => 0) point 2 2|
            |F (B n) (ψ n) point 3 3 - F Real.cos (fun _ => 0) point 3 3|) μ ≤ ENNReal.ofReal (δ n) ∧
      eLpNormEssSup (fun point => deriv (deriv (fun t =>
        F (B n) (ψ n) (Function.update point 0 t) 2 2)) (point 0)) μ ≤ ENNReal.ofReal (C / δ n) := by
  dsimp only
  let F := rosenMetricInCoordinates pulled
  let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
  let μ := volume.restrict (rosenScaleBox left right)
  rintro ⟨δ, C, hC, controls⟩
  have hfirst (f : Fin 4 → ℝ) (hf : f ∈ rosenScaleBox left right) : f 0 ∈ Icc left right := by
    simpa using hf 0 (mem_univ 0)
  have hJ : Icc left right ⊆ Ioo (-(1 / 3) : ℝ) (1 / 3) := by
    intro u hu
    obtain ⟨huL, huR⟩ := hsub hu
    exact ⟨by linarith, by linarith⟩
  have hp : ContinuousOn (fun f : Fin 4 → ℝ => f 0) (rosenScaleBox left right) :=
    (continuous_apply 0).continuousOn
  have hc : Set.MapsTo (fun f : Fin 4 → ℝ => f 0) (rosenScaleBox left right) (Ioo (-(1 / 3) : ℝ) (1 / 3)) :=
    fun f hf => hJ (hfirst f hf)
  apply rosen_no_common_metric_scale B hB hb left right hl hr hsub
  refine ⟨δ, C, ?_⟩
  filter_upwards [controls] with n hn
  obtain ⟨hd, ha, hh⟩ := hn
  let sx := fun u => screenX (B n u) (ψ n u)
  let sz := fun u => screenZ (B n u) (ψ n u)
  have hψ : ContDiff ℝ 2 (ψ n) := by
    unfold ψ phase scaledSine
    fun_prop
  have hsx : ContDiffOn ℝ 2 sx (Ioo (-(1 / 3) : ℝ) (1 / 3)) := by
    dsimp [sx, screenX]
    exact ((hB n).pow 2).mul ((contDiffOn_const.mul hψ.contDiffOn).exp)
  have hsz : ContDiffOn ℝ 2 sz (Ioo (-(1 / 3) : ℝ) (1 / 3)) := by
    dsimp [sz, screenZ]
    exact ((hB n).pow 2).mul ((contDiffOn_const.mul hψ.contDiffOn).exp)
  have hD : ContinuousOn (deriv (deriv sx)) (Ioo (-(1 / 3) : ℝ) (1 / 3)) :=
    (hsx.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have ha' : ∀ point ∈ rosenScaleBox left right,
      max |sx (point 0) - (Real.cos (point 0))^2| |sz (point 0) - (Real.cos (point 0))^2| ≤ δ n := by
    have hamp : (fun point => max |F (B n) (ψ n) point 2 2 - F Real.cos (fun _ => 0) point 2 2|
        |F (B n) (ψ n) point 3 3 - F Real.cos (fun _ => 0) point 3 3|) =
        (fun point => max |sx (point 0) - (Real.cos (point 0))^2|
                       |sz (point 0) - (Real.cos (point 0))^2|) := by
      funext point
      simp only [F, rosenMetricInCoordinates_xx, rosenMetricInCoordinates_zz, sx, sz]
      simp [screenX, screenZ]
    change eLpNormEssSup (fun point => max |F (B n) (ψ n) point 2 2 - F Real.cos (fun _ => 0) point 2 2|
      |F (B n) (ψ n) point 3 3 - F Real.cos (fun _ => 0) point 3 3|) μ ≤ _ at ha
    rw [hamp] at ha
    have hcos : ContinuousOn (fun f : Fin 4 → ℝ => (Real.cos (f 0))^2) (rosenScaleBox left right) :=
      (Real.continuous_cos.comp (continuous_apply 0)).continuousOn.pow 2
    have hcontinuity := ((hsx.continuousOn.comp hp hc).sub hcos).abs.sup
      ((hsz.continuousOn.comp hp hc).sub hcos).abs
    intro point hpoint
    exact (le_abs_self _).trans
      (rosenScaleBox_pointwise_of_essential_bound left right (hl.trans hr) _ hcontinuity _ hd.le ha point hpoint)
  have hh' : ∀ point ∈ rosenScaleBox left right, |deriv (deriv sx) (point 0)| ≤ C / δ n := by
    have hslice (point : Fin 4 → ℝ) : (fun t => F (B n) (ψ n) (Function.update point 0 t) 2 2) = sx := by
      funext t
      simp only [F, rosenMetricInCoordinates_xx, Function.update_self, sx]
    change eLpNormEssSup (fun point => deriv (deriv (fun t =>
      F (B n) (ψ n) (Function.update point 0 t) 2 2)) (point 0)) μ ≤ _ at hh
    simp only [hslice] at hh
    exact rosenScaleBox_pointwise_of_essential_bound left right (hl.trans hr) _ (hD.comp hp hc) _
      (div_nonneg hC hd.le) hh
  refine ⟨hd, fun u hu => ?_⟩
  let point : Fin 4 → ℝ := fun i => if i = 0 then u else 0
  have hpoint : point ∈ rosenScaleBox left right := by
    intro i _
    by_cases hi : i = 0
    · simpa [point, hi] using hu
    · simp [point, hi]
  have hzero : point 0 = u := by simp [point]
  have h := And.intro (ha' point hpoint) (hh' point hpoint)
  rwa [hzero] at h

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set

def rosenCoordinateSecondPartials (F : (Fin 4 → ℝ) → CoordinateMetric)
    (x : Fin 4 → ℝ) (a b i j : Fin 4) : ℝ :=
  deriv (fun t =>
    let y := Function.update x a t
    deriv (fun s => F (Function.update y b s) i j) (y b)) (x a)

theorem rosenCoordinateSecondPartials_same (F : (Fin 4 → ℝ) → CoordinateMetric)
    (x : Fin 4 → ℝ) (a i j : Fin 4) :
    rosenCoordinateSecondPartials F x a a i j =
      deriv (deriv (fun t => F (Function.update x a t) i j)) (x a) := by
  simp only [rosenCoordinateSecondPartials, Function.update_idem, Function.update_self]

/-- The maximum-entry norms use every metric entry and every pair of coordinate derivatives. -/
theorem rosen_no_common_full_metric_scale (B : ℕ → ℝ → ℝ)
    (hB : ∀ n, ContDiffOn ℝ 2 (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3)))
    (hb : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧ |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4)
    (pulled : Bool) (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hsub : Icc left right ⊆ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let F := rosenMetricInCoordinates pulled
    let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    let μ := volume.restrict (rosenScaleBox left right)
    ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      0 < δ n ∧
      eLpNormEssSup (fun x => ‖(fun i j => F (B n) (ψ n) x i j - F Real.cos (fun _ => 0) x i j)‖) μ ≤
        ENNReal.ofReal (δ n) ∧
      eLpNormEssSup (fun x => ‖rosenCoordinateSecondPartials (F (B n) (ψ n)) x‖) μ ≤
        ENNReal.ofReal (C / δ n) := by
  dsimp only
  let F := rosenMetricInCoordinates pulled
  let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
  let μ := volume.restrict (rosenScaleBox left right)
  rintro ⟨δ, C, hC, controls⟩
  apply rosen_no_common_essential_metric_scale B hB hb pulled left right hl hr hsub
  refine ⟨δ, C, hC, ?_⟩
  filter_upwards [controls] with n hn
  obtain ⟨hd, ha, hh⟩ := hn
  let A := fun x (i j : Fin 4) => F (B n) (ψ n) x i j - F Real.cos (fun _ => 0) x i j
  let H := rosenCoordinateSecondPartials (F (B n) (ψ n))
  have ha_dom : eLpNormEssSup (fun x => max |A x 2 2| |A x 3 3|) μ ≤
      eLpNormEssSup (fun x => ‖A x‖) μ := by
    apply eLpNormEssSup_mono_enorm_ae
    apply Eventually.of_forall
    intro x
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    have h (i : Fin 4) : |A x i i| ≤ ‖A x‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (A x i) i).trans (norm_le_pi_norm (A x) i)
    exact max_le (h 2) (h 3)
  have hh_dom : eLpNormEssSup (fun x =>
      deriv (deriv (fun t => F (B n) (ψ n) (Function.update x 0 t) 2 2)) (x 0)) μ ≤
      eLpNormEssSup (fun x => ‖H x‖) μ := by
    apply eLpNormEssSup_mono_enorm_ae
    apply Eventually.of_forall
    intro x
    rw [← rosenCoordinateSecondPartials_same]
    change ‖H x 0 0 2 2‖ₑ ≤ ‖‖H x‖‖ₑ
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← Real.norm_eq_abs (H x 0 0 2 2), abs_of_nonneg (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    exact (norm_le_pi_norm (H x 0 0 2) 2).trans ((norm_le_pi_norm (H x 0 0) 2).trans
      ((norm_le_pi_norm (H x 0) 0).trans (norm_le_pi_norm (H x) 0)))
  exact ⟨hd, ha_dom.trans ha, hh_dom.trans hh⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set

theorem rosenScaleBox_point_le_essential_norm (left right : ℝ) (hlt : left < right)
    (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f (rosenScaleBox left right))
    (x : Fin 4 → ℝ) (hx : x ∈ rosenScaleBox left right) :
    ENNReal.ofReal |f x| ≤ eLpNormEssSup f (volume.restrict (rosenScaleBox left right)) := by
  let e := eLpNormEssSup f (volume.restrict (rosenScaleBox left right))
  change ENNReal.ofReal |f x| ≤ e
  by_cases ht : e = ⊤
  · exact ht.symm ▸ le_top
  · have he : ENNReal.ofReal e.toReal = e := ENNReal.ofReal_toReal ht
    have h := rosenScaleBox_pointwise_of_essential_bound left right hlt f hf e.toReal
      ENNReal.toReal_nonneg (le_of_eq he.symm) x hx
    rw [← he]
    exact ENNReal.ofReal_le_ofReal h

theorem rosen_full_metric_essential_lower_bounds (B : ℕ → ℝ → ℝ)
    (hB : ∀ n, ContDiffOn ℝ 2 (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3)))
    (hb : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧ |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4)
    (pulled : Bool) (left right : ℝ) (hl : left < 0) (hr : 0 < right)
    (hsub : Icc left right ⊆ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    let F := rosenMetricInCoordinates pulled
    let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    let μ := volume.restrict (rosenScaleBox left right)
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((Real.cos (1/2))^2 / (2 * ((n : ℝ) + 1))) ≤
        eLpNormEssSup (fun x => ‖(fun i j => F (B n) (ψ n) x i j - F Real.cos (fun _ => 0) x i j)‖) μ ∧
      ENNReal.ofReal (2 * Real.exp (-4) * (Real.cos (1/2))^2 * Real.exp ((n : ℝ) + 1) - 42 * Real.exp 4) ≤
        eLpNormEssSup (fun x => ‖rosenCoordinateSecondPartials (F (B n) (ψ n)) x‖) μ := by
  dsimp only
  let F := rosenMetricInCoordinates pulled
  let ψ := fun (n : ℕ) => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
  let μ := volume.restrict (rosenScaleBox left right)
  let J := Icc (-(1 / 4) : ℝ) (1 / 4)
  let U := Ioo (-(1 / 3) : ℝ) (1 / 3)
  have hJU : J ⊆ U := by
    intro u hu
    exact ⟨lt_of_lt_of_le (by norm_num) hu.1, lt_of_le_of_lt hu.2 (by norm_num)⟩
  have hp : ContinuousOn (fun x : Fin 4 → ℝ => x 0) (rosenScaleBox left right) :=
    (continuous_apply 0).continuousOn
  have hmap : MapsTo (fun x : Fin 4 → ℝ => x 0) (rosenScaleBox left right) U := fun x hx =>
    hJU (hsub (by simpa using hx 0 (mem_univ 0)))
  let sample : ℝ → Fin 4 → ℝ := fun u i => if i = 0 then u else 0
  have hs0 (u : ℝ) : sample u 0 = u := by simp [sample]
  have hsBox (u : ℝ) (hu : u ∈ Icc left right) : sample u ∈ rosenScaleBox left right := by
    intro i _
    by_cases h : i = 0
    · simpa [sample, h] using hu
    · simp [sample, h]
  filter_upwards [rosen_sampling_points_eventually_mem left right hl hr] with n hn
  obtain ⟨hslow, hfast⟩ := hn
  let a := (n : ℝ) + 1
  let A := fun x (i j : Fin 4) => F (B n) (ψ n) x i j - F Real.cos (fun _ => 0) x i j
  let H := rosenCoordinateSecondPartials (F (B n) (ψ n))
  let sx := fun u => screenX (B n u) (ψ n u)
  let sz := fun u => screenZ (B n u) (ψ n u)
  have hψ : ContDiff ℝ 2 (ψ n) := by
    unfold ψ phase scaledSine
    fun_prop
  have hsx : ContDiffOn ℝ 2 sx U := (hB n).pow 2 |>.mul ((contDiffOn_const.mul hψ.contDiffOn).exp)
  have hsz : ContDiffOn ℝ 2 sz U := (hB n).pow 2 |>.mul ((contDiffOn_const.mul hψ.contDiffOn).exp)
  have hcos : ContinuousOn (fun x : Fin 4 → ℝ => (Real.cos (x 0))^2) (rosenScaleBox left right) :=
    (Real.continuous_cos.comp (continuous_apply 0)).continuousOn.pow 2
  have hD : ContinuousOn (deriv (deriv sx)) U :=
    (hsx.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  let f := fun x : Fin 4 → ℝ => max |sx (x 0) - (Real.cos (x 0))^2| |sz (x 0) - (Real.cos (x 0))^2|
  let d := fun x : Fin 4 → ℝ => deriv (deriv sx) (x 0)
  have hfa : ContinuousOn f (rosenScaleBox left right) :=
    ((hsx.continuousOn.comp hp hmap).sub hcos).abs.sup ((hsz.continuousOn.comp hp hmap).sub hcos).abs
  have hda : ContinuousOn d (rosenScaleBox left right) := hD.comp hp hmap
  have hfpoint (x : Fin 4 → ℝ) : f x = max |A x 2 2| |A x 3 3| := by
    simp only [f, A, F, rosenMetricInCoordinates_xx, rosenMetricInCoordinates_zz, sx, sz]
    simp [screenX, screenZ]
  have hdpoint (x : Fin 4 → ℝ) : d x = H x 0 0 2 2 := by
    rw [show H x 0 0 2 2 = _ from rosenCoordinateSecondPartials_same _ x 0 2 2]
    have hslice : (fun t => F (B n) (ψ n) (Function.update x 0 t) 2 2) = sx := by
      funext t
      simp only [F, rosenMetricInCoordinates_xx, Function.update_self, sx]
    simp [d, hslice]
  have hfd (x : Fin 4 → ℝ) : |f x| ≤ ‖A x‖ := by
    rw [hfpoint, abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    have hdiag (i : Fin 4) : |A x i i| ≤ ‖A x‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (A x i) i).trans (norm_le_pi_norm (A x) i)
    exact max_le (hdiag 2) (hdiag 3)
  have hdd (x : Fin 4 → ℝ) : |d x| ≤ ‖H x‖ := by
    rw [hdpoint, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (H x 0 0 2) 2).trans ((norm_le_pi_norm (H x 0 0) 2).trans
      ((norm_le_pi_norm (H x 0) 0).trans (norm_le_pi_norm (H x) 0)))
  have hes (g : (Fin 4 → ℝ) → ℝ) (v : (Fin 4 → ℝ) → ℝ) (h : ∀ x, |g x| ≤ v x)
      (hv : ∀ x, 0 ≤ v x) : eLpNormEssSup g μ ≤ eLpNormEssSup v μ := by
    apply eLpNormEssSup_mono_enorm_ae
    exact Eventually.of_forall fun x => by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hv x)]
      exact ENNReal.ofReal_le_ofReal (h x)
  let xs := sample (Real.pi / (2 * a))
  let xd := sample (Real.pi / (2 * Real.exp a))
  have hpos : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hfl := rosen_metric_amplitude_lower_at_peak a hpos (B n) (fun u hu => (hb n u hu).1) (hsub hslow)
  have hdl := rosen_metric_hessian_lower_at_fast_peak a ha1 (B n) U isOpen_Ioo (hB n) hJU (hb n) (hsub hfast)
  have haf : (Real.cos (1/2))^2 / (2 * a) ≤ |f xs| := by
    apply le_trans ?_ (le_abs_self _)
    simpa only [f, xs, hs0, sx, sz, ψ, a] using hfl
  have had : 2 * Real.exp (-4) * (Real.cos (1/2))^2 * Real.exp a - 42 * Real.exp 4 ≤ |d xd| := by
    simpa only [d, xd, hs0, sx, ψ, a] using hdl
  exact ⟨(ENNReal.ofReal_le_ofReal haf).trans
      ((rosenScaleBox_point_le_essential_norm left right (hl.trans hr) f hfa xs (hsBox _ hslow)).trans
        (hes f (fun x => ‖A x‖) hfd fun _ => norm_nonneg _)),
    (ENNReal.ofReal_le_ofReal had).trans
      ((rosenScaleBox_point_le_essential_norm left right (hl.trans hr) d hda xd (hsBox _ hfast)).trans
        (hes d (fun x => ‖H x‖) hdd fun _ => norm_nonneg _))⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter Set
open scoped ContDiff Topology

theorem abs_exp_phase_le (a u : ℝ) (ha : 0 < a) :
    |phase a (Real.exp a) u| ≤ 2 / a := by
  unfold phase
  calc
    |scaledSine a u + scaledSine (Real.exp a) u| ≤
        |scaledSine a u| + |scaledSine (Real.exp a) u| := abs_add_le _ _
    _ ≤ 1 / a + 1 / a := by
      refine add_le_add ?_ ?_
      · simpa [abs_of_pos ha] using abs_scaledSine_le a u
      · refine (abs_scaledSine_le _ _).trans ?_
        rw [abs_of_pos (Real.exp_pos a)]
        exact one_div_le_one_div_of_le ha (by linarith [two_mul_le_exp_of_nonneg a ha.le])
    _ = 2 / a := by ring

private theorem polarizedScreen_hasDerivAt (B ψ : ℝ → ℝ) (u σ : ℝ)
    (hB : DifferentiableAt ℝ B u) (hψ : DifferentiableAt ℝ ψ u) :
    HasDerivAt (fun t => (B t)^2 * Real.exp (σ * ψ t))
      ((2 * B u * deriv B u + (B u)^2 * (σ * deriv ψ u)) *
        Real.exp (σ * ψ u)) u := by
  convert (hB.hasDerivAt.pow 2).mul (hψ.hasDerivAt.const_mul σ).exp using 1
  simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Pi.pow_apply]
  ring

private theorem polarizedScreen_first_bound (B : ℝ → ℝ) (u σ : ℝ)
    (n : ℕ) (hσ : |σ| ≤ 2) (hB : |B u| ≤ 1) (hB' : |deriv B u| ≤ 1) :
    let ψ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    |(2 * B u * deriv B u + (B u)^2 * (σ * deriv ψ u)) *
        Real.exp (σ * ψ u)| ≤ 6 * Real.exp 4 := by
  let a : ℝ := (n : ℝ) + 1
  let ψ := phase a (Real.exp a)
  have ha₁ : 1 ≤ a := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have ha : 0 < a := by linarith
  have hψ : |ψ u| ≤ 2 := (abs_exp_phase_le a u ha).trans
    (div_le_iff₀ ha |>.mpr (by linarith))
  have hψ' : |deriv ψ u| ≤ 2 := by
    have h := (exp_phase_deriv_sq_mem_Icc a u ha).2
    change deriv ψ u ^ 2 ≤ 4 at h
    rw [← sq_abs] at h
    nlinarith [abs_nonneg (deriv ψ u)]
  have hpow : |B u| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (B u)]
  have hexponent : |σ * ψ u| ≤ 4 := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hσ hψ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : Real.exp (σ * ψ u) ≤ Real.exp 4 :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans hexponent)
  have h1 : |2 * B u * deriv B u| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |B u| * |deriv B u| ≤ 2 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hB'
          (abs_nonneg _) (by norm_num)
      _ = 2 := by ring
  have h2 : |(B u)^2 * (σ * deriv ψ u)| ≤ 4 := by
    rw [abs_mul, abs_pow, abs_mul]
    calc
      |B u| ^ 2 * (|σ| * |deriv ψ u|) ≤ 1 * (2 * 2) :=
        mul_le_mul hpow (mul_le_mul hσ hψ' (abs_nonneg _) (by norm_num))
          (by positivity) (by norm_num)
      _ = 4 := by ring
  change |(2 * B u * deriv B u + (B u)^2 * (σ * deriv ψ u)) *
      Real.exp (σ * ψ u)| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul ((abs_add_le _ _).trans (by linarith only [h1, h2])) hexp
    (Real.exp_pos _).le (by norm_num)

private theorem polarizedScreen_uniform (B : ℕ → ℝ → ℝ) (σ : ℝ) (hσ : |σ| ≤ 2)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |B n u| ≤ 1)
    (hlim : TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4))) :
    TendstoUniformlyOn
      (fun n u => (B n u)^2 *
        Real.exp (σ * phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1)) u))
      (fun u => (Real.cos u)^2) atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  obtain ⟨δ, hδ, hExp⟩ := Metric.continuousAt_iff.mp
    Real.continuous_exp.continuousAt (ε / 2) (by positivity)
  have hRate : Tendsto (fun n : ℕ => 4 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)
  have hEvent := Metric.tendsto_nhds.mp hRate δ hδ
  filter_upwards [hlim (ε / 4) (by positivity), hEvent] with n hn hr u hu
  let a : ℝ := (n : ℝ) + 1
  let θ := σ * phase a (Real.exp a) u
  let b := B n u
  let c := Real.cos u
  have ha : 0 < a := by unfold a; positivity
  have hθ : |θ| ≤ 4 * (1 / a) := by
    dsimp only [θ]
    rw [abs_mul]
    calc
      |σ| * |phase a (Real.exp a) u| ≤ 2 * (2 / a) :=
        mul_le_mul hσ (abs_exp_phase_le a u ha) (abs_nonneg _) (by norm_num)
      _ = 4 * (1 / a) := by ring
  have hθδ : dist θ 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ 4 * (1 / ((n : ℝ) + 1)))] at hr
    exact hθ.trans_lt hr
  have hE : |Real.exp θ - 1| < ε / 2 := by
    simpa [Real.dist_eq] using hExp hθδ
  have hbc : |b - c| < ε / 4 := by
    simpa [Real.dist_eq, abs_sub_comm, b, c] using hn u hu
  have hb := hB n u hu
  have hc := Real.abs_cos_le_one u
  have hBsq : |b ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg b, show |b| ≤ 1 from hb]
  have hbcSum : |b + c| ≤ 2 := (abs_add_le _ _).trans (by
    linarith only [show |b| ≤ 1 from hb, show |c| ≤ 1 from hc])
  have hdc : |b ^ 2 - c ^ 2| ≤ 2 * |b - c| := by
    rw [show b ^ 2 - c ^ 2 = (b - c) * (b + c) by ring, abs_mul, mul_comm 2]
    exact mul_le_mul_of_nonneg_left hbcSum (abs_nonneg _)
  have he : |b^2 * (Real.exp θ - 1)| ≤ |Real.exp θ - 1| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hBsq (abs_nonneg (Real.exp θ - 1))
  change dist (c^2) (b^2 * Real.exp θ) < ε
  rw [dist_comm, Real.dist_eq, show b^2 * Real.exp θ - c^2 =
      b^2 * (Real.exp θ - 1) + (b^2 - c^2) by ring]
  exact (abs_add_le _ _).trans_lt (by linarith only [hE, hbc, hdc, he])

theorem originalRosen_uniform_metric (B : ℕ → ℝ → ℝ)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |B n u| ≤ 1)
    (hlim : TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4))) :
    TendstoUniformlyOn
      (fun n (point : Fin 4 → ℝ) (i j : Fin 4) =>
         originalRosenField (B n) (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) point i j)
      (fun (point : Fin 4 → ℝ) (i j : Fin 4) =>
         originalRosenField Real.cos (fun _ => 0) point i j)
      atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4)} := by
  have hX := polarizedScreen_uniform B 2 (by norm_num) hB hlim
  have hZ := polarizedScreen_uniform B (-2) (by norm_num) hB hlim
  rw [Metric.tendstoUniformlyOn_iff] at hX hZ ⊢
  intro ε hε
  filter_upwards [hX (ε / 2) (by positivity), hZ (ε / 2) (by positivity)] with n hnX hnZ p hp
  have hhalf : 0 ≤ ε / 2 := by positivity
  refine lt_of_le_of_lt ((dist_pi_le_iff hhalf).mpr ?_) (by linarith)
  intro i
  refine (dist_pi_le_iff hhalf).mpr ?_
  intro j
  have hx := (hnX (p 0) hp).le
  have hz := (hnZ (p 0) hp).le
  simp only [neg_mul] at hz
  fin_cases i <;> fin_cases j <;>
    simp [originalRosenField, screenX, screenZ, hhalf, hx, hz]

theorem originalRosen_first_coordinates (B : ℕ → ℝ → ℝ)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      DifferentiableAt ℝ (B n) u ∧ |B n u| ≤ 1 ∧ |deriv (B n) u| ≤ 1) :
    ∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      ∀ i j k : Fin 4, ∃ d : ℝ,
        HasDerivAt (fun t => originalRosenField (B n)
          (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) (Function.update point k t) i j)
          d (point k) ∧ |d| ≤ 6 * Real.exp 4 := by
  intro n p hp i j k
  let a : ℝ := (n : ℝ) + 1
  let ψ := phase a (Real.exp a)
  change ∃ d : ℝ, HasDerivAt (fun t => originalRosenField (B n) ψ
    (Function.update p k t) i j) d (p k) ∧ |d| ≤ _
  have ha : 0 < a := by unfold a; positivity
  have hψ : DifferentiableAt ℝ ψ (p 0) :=
    (phase_hasDerivAt a (Real.exp a) (p 0) ha.ne' (Real.exp_pos a).ne').differentiableAt
  obtain ⟨hd, hb, hb'⟩ := hB n (p 0) hp
  have hX : ∃ d, HasDerivAt (fun t => screenX (B n t) (ψ t)) d (p 0) ∧
      |d| ≤ 6 * Real.exp 4 := by
    exact ⟨_, polarizedScreen_hasDerivAt (B n) ψ (p 0) 2 hd hψ,
      polarizedScreen_first_bound (B n) (p 0) 2 n (by norm_num) hb hb'⟩
  have hZ : ∃ d, HasDerivAt (fun t => screenZ (B n t) (ψ t)) d (p 0) ∧
      |d| ≤ 6 * Real.exp 4 := by
    exact ⟨_, polarizedScreen_hasDerivAt (B n) ψ (p 0) (-2) hd hψ,
      polarizedScreen_first_bound (B n) (p 0) (-2) n (by norm_num) hb hb'⟩
  have hconst (c x : ℝ) : ∃ d : ℝ, HasDerivAt (fun _ : ℝ => c) d x ∧
      |d| ≤ 6 * Real.exp 4 :=
    ⟨0, hasDerivAt_const x c, by rw [abs_zero]; positivity⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [originalRosenField, Function.update_of_ne, hX, hZ, hconst]


theorem exists_smooth_rosen_sequence_c1_zero_source_and_original_metric :
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
        (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      let ψ := fun n : ℕ => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
      (∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        let J := coordinateJacobian (rosenCoordinates (B n)) point
        (J.transpose * originalRosenField (B n) (ψ n) (rosenCoordinates (B n) point) * J =
          pulledRosenField (B n) (ψ n) point) ∧ ∀ i, contractedSource (B n) (ψ n) point i = 0) ∧
      TendstoUniformlyOn
        (fun n (point : Fin 4 → ℝ) (i j : Fin 4) => originalRosenField (B n) (ψ n) point i j)
        (fun (point : Fin 4 → ℝ) (i j : Fin 4) =>
          originalRosenField Real.cos (fun _ => 0) point i j)
        atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4)} ∧
      ∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        ∀ i j k : Fin 4, ∃ d : ℝ,
          HasDerivAt (fun t => originalRosenField (B n) (ψ n) (Function.update point k t) i j)
            d (point k) ∧ |d| ≤ 6 * Real.exp 4 := by
  obtain ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim', hzero⟩ :=
    exists_smooth_rosen_sequence_c1_and_zero_source
  have hval (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) : |B n u| ≤ 1 := by
    obtain ⟨hcos, hcomp, hupper, _⟩ := hbounds n u hu
    simpa [abs_of_pos (hcos.trans_le hcomp)] using hupper
  have hdiff (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      DifferentiableAt ℝ (B n) u := by
    have hi : u ∈ Ioo (-(1 / 3) : ℝ) (1 / 3) :=
      ⟨lt_of_lt_of_le (by norm_num) hu.1, lt_of_le_of_lt hu.2 (by norm_num)⟩
    exact ((contDiffOn_infty.mp (hs n) 1).contDiffAt
      (isOpen_Ioo.mem_nhds hi)).differentiableAt (by norm_num)
  exact ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim', hzero,
    originalRosen_uniform_metric B hval hlim,
    originalRosen_first_coordinates B (fun n u hu =>
      ⟨hdiff n u hu, hval n u hu, (hbounds n u hu).2.2.2.1⟩)⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter Set
open scoped ContDiff Topology

theorem pulledRosen_uniform_metric (B : ℕ → ℝ → ℝ)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |B n u| ≤ 1)
    (hlim : TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4)))
    (hlim' : TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop
      (Icc (-(1 / 4) : ℝ) (1 / 4))) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun n (point : Fin 4 → ℝ) (i j : Fin 4) =>
         pulledRosenField (B n) (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) point i j)
      (fun (point : Fin 4 → ℝ) (i j : Fin 4) => pulledRosenField Real.cos (fun _ => 0) point i j)
      atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) ∧ |point 1| ≤ R} := by
  have ho := originalRosen_uniform_metric B hB hlim
  rw [Metric.tendstoUniformlyOn_iff] at ho hlim hlim' ⊢
  intro ε hε
  let e := ε / 2
  let K := 2 * (R + 1)
  have he : 0 < e := by dsimp [e]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  filter_upwards [ho e he, hlim e he, hlim' (e / K) (div_pos he hK)] with n hnO hnB hnD p hp
  have hhalf : 0 ≤ e := he.le
  obtain ⟨hu, hv⟩ := hp
  have hO := (dist_pi_le_iff hhalf).mp (hnO p hu).le
  let ψ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
  have hx : dist (screenX (Real.cos (p 0)) 0) (screenX (B n (p 0)) (ψ (p 0))) ≤ e := by
    simpa [originalRosenField] using (dist_pi_le_iff hhalf).mp (hO 2) 2
  have hz : dist (screenZ (Real.cos (p 0)) 0) (screenZ (B n (p 0)) (ψ (p 0))) ≤ e := by
    simpa [originalRosenField] using (dist_pi_le_iff hhalf).mp (hO 3) 3
  have hm := (hnB (p 0) hu).le
  have hd : |deriv (B n) (p 0) - deriv Real.cos (p 0)| ≤ e / K := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hnD (p 0) hu).le
  have hvK : 2 * |p 1| ≤ K := by dsimp [K]; linarith
  have huu : dist (-2 * deriv Real.cos (p 0) * p 1)
      (-2 * deriv (B n) (p 0) * p 1) ≤ e := by
    rw [Real.dist_eq, show -2 * deriv Real.cos (p 0) * p 1 - -2 * deriv (B n) (p 0) * p 1 =
      (deriv (B n) (p 0) - deriv Real.cos (p 0)) * (2 * p 1) by ring,
      abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (e / K) * K := mul_le_mul hd hvK (by positivity) (by positivity)
      _ = e := div_mul_cancel₀ e hK.ne'
  refine lt_of_le_of_lt ((dist_pi_le_iff hhalf).mpr ?_) (by dsimp [e]; linarith)
  intro i
  refine (dist_pi_le_iff hhalf).mpr ?_
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [pulledRosenField, pulledMetricAt, hm, hhalf] <;>
    first | exact hx | exact hz | simpa using huu

theorem pulledRosen_first_coordinates (B : ℕ → ℝ → ℝ)
    (hB : ∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
      DifferentiableAt ℝ (B n) u ∧ DifferentiableAt ℝ (deriv (B n)) u ∧
      |B n u| ≤ 1 ∧ |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4)
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ (n : ℕ) (point : Fin 4 → ℝ),
      point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |point 1| ≤ R →
      ∀ i j k : Fin 4, ∃ d : ℝ,
        HasDerivAt (fun t => pulledRosenField (B n)
          (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) (Function.update point k t) i j)
          d (point k) ∧ |d| ≤ 8 * R + 2 + 6 * Real.exp 4 := by
  let C := 8 * R + 2 + 6 * Real.exp 4
  have hC1 : (1 : ℝ) ≤ C := by dsimp [C]; linarith [Real.exp_pos (4 : ℝ)]
  have hC2 : (2 : ℝ) ≤ C := by dsimp [C]; linarith [Real.exp_pos (4 : ℝ)]
  have hCs : 6 * Real.exp 4 ≤ C := by dsimp [C]; linarith
  have hCuu : 8 * R ≤ C := by dsimp [C]; linarith [Real.exp_pos (4 : ℝ)]
  intro n p hu hv i j k
  let ψ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
  have horig := originalRosen_first_coordinates B (fun m t ht =>
    ⟨(hB m t ht).1, (hB m t ht).2.2.1, (hB m t ht).2.2.2.1⟩) n p hu
  obtain ⟨hBd, hBdd, _, hB', hB''⟩ := hB n (p 0) hu
  have hX : ∃ d, HasDerivAt (fun t => screenX (B n t) (ψ t)) d (p 0) ∧ |d| ≤ C := by
    obtain ⟨d, hd, hb⟩ := horig 2 2 0
    exact ⟨d, by simpa [originalRosenField] using hd, hb.trans hCs⟩
  have hZ : ∃ d, HasDerivAt (fun t => screenZ (B n t) (ψ t)) d (p 0) ∧ |d| ≤ C := by
    obtain ⟨d, hd, hb⟩ := horig 3 3 0
    exact ⟨d, by simpa [originalRosenField] using hd, hb.trans hCs⟩
  have huv : ∃ d, HasDerivAt (fun t => -B n t) d (p 0) ∧ |d| ≤ C :=
    ⟨-deriv (B n) (p 0), hBd.hasDerivAt.neg, by rw [abs_neg]; exact hB'.trans hC1⟩
  have huu : ∃ d, HasDerivAt (fun t => -2 * deriv (B n) t * p 1) d (p 0) ∧ |d| ≤ C := by
    refine ⟨-2 * deriv (deriv (B n)) (p 0) * p 1,
      (hBdd.hasDerivAt.const_mul (-2 : ℝ)).mul_const (p 1), ?_⟩
    rw [abs_mul, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    calc
      2 * |deriv (deriv (B n)) (p 0)| * |p 1| ≤ 2 * 4 * R :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB'' (by norm_num)) hv (by positivity) (by norm_num)
      _ = 8 * R := by ring
      _ ≤ C := hCuu
  have huuV : ∃ d, HasDerivAt (fun t => -2 * deriv (B n) (p 0) * t) d (p 1) ∧ |d| ≤ C := by
    refine ⟨-2 * deriv (B n) (p 0), ?_, ?_⟩
    · simpa only [id_eq, mul_one] using
        (hasDerivAt_id (p 1)).const_mul (-2 * deriv (B n) (p 0))
    · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
      linarith
  have hconst (c x : ℝ) : ∃ d : ℝ, HasDerivAt (fun _ : ℝ => c) d x ∧ |d| ≤ C :=
    ⟨0, hasDerivAt_const x c, by rw [abs_zero]; linarith⟩
  change ∃ d, HasDerivAt (fun t => pulledRosenField (B n) ψ (Function.update p k t) i j)
    d (p k) ∧ |d| ≤ C
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [pulledRosenField, pulledMetricAt, Function.update_of_ne, hX, hZ, huv, hconst] <;>
    first | simpa using huu | simpa using huuV


theorem exists_smooth_rosen_sequence_c1_zero_source_and_both_metrics :
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
        (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      let ψ := fun n : ℕ => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
      (∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        let J := coordinateJacobian (rosenCoordinates (B n)) point
        (J.transpose * originalRosenField (B n) (ψ n) (rosenCoordinates (B n) point) * J =
          pulledRosenField (B n) (ψ n) point) ∧ ∀ i, contractedSource (B n) (ψ n) point i = 0) ∧
      TendstoUniformlyOn
        (fun n (point : Fin 4 → ℝ) (i j : Fin 4) => originalRosenField (B n) (ψ n) point i j)
        (fun (point : Fin 4 → ℝ) (i j : Fin 4) =>
          originalRosenField Real.cos (fun _ => 0) point i j)
        atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4)} ∧
      (∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        ∀ i j k : Fin 4, ∃ d : ℝ,
          HasDerivAt (fun t => originalRosenField (B n) (ψ n) (Function.update point k t) i j)
            d (point k) ∧ |d| ≤ 6 * Real.exp 4) ∧
      ∀ R ≥ 0,
        TendstoUniformlyOn
          (fun n (point : Fin 4 → ℝ) (i j : Fin 4) => pulledRosenField (B n) (ψ n) point i j)
          (fun (point : Fin 4 → ℝ) (i j : Fin 4) =>
            pulledRosenField Real.cos (fun _ => 0) point i j)
          atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) ∧ |point 1| ≤ R} ∧
        ∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |point 1| ≤ R →
          ∀ i j k : Fin 4, ∃ d : ℝ,
            HasDerivAt (fun t => pulledRosenField (B n) (ψ n) (Function.update point k t) i j)
              d (point k) ∧ |d| ≤ 8 * R + 2 + 6 * Real.exp 4 := by
  obtain ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim', hzero, horig, horig'⟩ :=
    exists_smooth_rosen_sequence_c1_zero_source_and_original_metric
  have hval (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) : |B n u| ≤ 1 := by
    obtain ⟨hcos, hcomp, hupper, _⟩ := hbounds n u hu
    simpa [abs_of_pos (hcos.trans_le hcomp)] using hupper
  have hdiff (n : ℕ) (u : ℝ) (hu : u ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
      DifferentiableAt ℝ (B n) u ∧ DifferentiableAt ℝ (deriv (B n)) u := by
    have hi : u ∈ Ioo (-(1 / 3) : ℝ) (1 / 3) :=
      ⟨lt_of_lt_of_le (by norm_num) hu.1, lt_of_le_of_lt hu.2 (by norm_num)⟩
    have hOn := contDiffOn_infty.mp (hs n) 2
    have hDeriv := ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).mp hOn).2.2
    exact ⟨(hOn.contDiffAt (isOpen_Ioo.mem_nhds hi)).differentiableAt (by norm_num),
      (hDeriv.contDiffAt (isOpen_Ioo.mem_nhds hi)).differentiableAt (by norm_num)⟩
  refine ⟨B, hB, hB', hs, hODE, hbounds, hlim, hlim', hzero, horig, horig', ?_⟩
  intro R hR
  exact ⟨pulledRosen_uniform_metric B hval hlim hlim' R hR,
    pulledRosen_first_coordinates B (fun n u hu =>
      ⟨(hdiff n u hu).1, (hdiff n u hu).2, hval n u hu, (hbounds n u hu).2.2.2⟩) R hR⟩

end Burnett.RosenMultiscale
