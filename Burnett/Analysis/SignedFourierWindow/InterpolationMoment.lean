import Burnett.Analysis.SignedFourierWindow.InterpolationLevel
import Burnett.Analysis.SignedFourierWindow.InterpolationBottom

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set
open scoped ENNReal

/-- Integrated Marcinkiewicz estimate with its finite p-dependent constants.
Here one may take any Borel, integrable input; the right side is finite for L¹∩Lᵖ. -/
theorem kernel_interpolation_moment (K : Space → ℂ) (hK : Continuous K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    (W B : ℝ≥0∞)
    (weak : ∀ h : Space → ℂ, Integrable h → ∀ t : ℝ, 0<t →
      ENNReal.ofReal t * volume {x | t < ‖kernelApply K h x‖} ≤ W * ∫⁻ x, ‖h x‖ₑ)
    (strong : ∀ l : Space → ℂ, MemLp l 2 volume → eLpNorm (kernelApply K l) 2 volume ≤ B*eLpNorm l 2 volume)
    (f : Space → ℂ) (hm : Measurable f) (hf : Integrable f) (p : ℝ) (hp : 1<p) (hp2 : p<2) :
    (∫⁻ x, ‖kernelApply K f x‖ₑ^p) ≤
      (ENNReal.ofReal ((2:ℝ)^p*p) * (W*ENNReal.ofReal (p-1)⁻¹+B^2*ENNReal.ofReal (2-p)⁻¹)) *
        ∫⁻ x, ‖f x‖ₑ^p := by
  classical
  let F := fun x : Space => ‖kernelApply K f x‖/2
  let g := fun x : Space => ‖f x‖
  let G := fun x : Space => ENNReal.ofReal (g x)
  let H := fun t : ℝ => (∫⁻ x, upperTail G (ENNReal.ofReal t) x)*ENNReal.ofReal (t^(p-1-1))
  let L := fun t : ℝ => (∫⁻ x in {x : Space | g x ≤ t}, (G x)^2)*ENNReal.ofReal (t^(p-3))
  let c := (2:ℝ)^p*p
  have hp0 : 0<p := by linarith
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hp0.le
  have hmF : Measurable F := (measurable_kernelApply K f hK hm).norm.div_const _
  have hnF (x : Space) : 0 ≤ F x := div_nonneg (norm_nonneg _) (by norm_num)
  have hmg : Measurable g := hm.norm
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hmg
  have mh : Measurable H := by
    have joint : Measurable (fun z : ℝ × Space => upperTail G (ENNReal.ofReal z.1) z.2) :=
      Measurable.ite (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hG.comp measurable_snd)) (hG.comp measurable_snd) measurable_const
    exact joint.lintegral_prod_right.mul (by fun_prop)
  have ml : Measurable L := by
    let j := fun (t : ℝ) (x : Space) => if g x ≤ t then (G x)^2 else 0
    have jmeas : Measurable (Function.uncurry j) := Measurable.ite
      (measurableSet_le (hmg.comp measurable_snd) measurable_fst) ((hG.comp measurable_snd).pow_const 2) measurable_const
    have he (t : ℝ) : (∫⁻ x in {x : Space | g x ≤ t}, (G x)^2) = ∫⁻ x, j t x := by
      rw [← lintegral_indicator (measurableSet_le hmg measurable_const)]; rfl
    dsimp only [L]; simp_rw [he]
    exact jmeas.lintegral_prod_right.mul (by fun_prop)
  have power (x : Space) : ‖kernelApply K f x‖ₑ^p = ENNReal.ofReal c * ENNReal.ofReal ((F x)^p/p) := by
    rw [← ofReal_norm_eq_enorm,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,← ENNReal.ofReal_mul hc]
    congr 1
    dsimp only [F,c]
    rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    field_simp [hp0.ne',(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p).ne']
  have top (x : Space) : G x*ENNReal.ofReal ((g x)^(p-1)/(p-1)) = ENNReal.ofReal (p-1)⁻¹*(G x)^p := by
    have hn : 0 ≤ g x := norm_nonneg _
    rw [show G x = ENNReal.ofReal (g x) from rfl,← ENNReal.ofReal_mul hn,
      ENNReal.ofReal_rpow_of_nonneg hn hp0.le,← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]
    congr 1
    have hpow := Real.rpow_add_one' (x := g x) (y := p-1) hn (by linarith)
    rw [sub_add_cancel] at hpow
    rw [hpow,div_eq_mul_inv]; ring
  have ih : (∫⁻ t in Ioi (0:ℝ), H t) = ENNReal.ofReal (p-1)⁻¹ * ∫⁻ x, (G x)^p := by
    rw [show (∫⁻ t in Ioi (0:ℝ), H t) = ∫⁻ x, G x * ENNReal.ofReal ((g x)^(p-1)/(p-1)) from
      integrated_tail_power g hmg (fun x => norm_nonneg _) (p-1) (by linarith)]
    simp_rw [top]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have il : (∫⁻ t in Ioi (0:ℝ), L t) = ENNReal.ofReal (2-p)⁻¹ * ∫⁻ x, (G x)^p :=
    integrated_lower_square g hmg (fun x => norm_nonneg _) p hp hp2
  have distrib := power_distribution volume F hmF hnF p hp0
  simp_rw [power]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,distrib]
  have levels : (∫⁻ t in Ioi (0:ℝ), volume {x | t < F x}*ENNReal.ofReal (t^(p-1))) ≤
      ∫⁻ t in Ioi (0:ℝ), W*H t + B^2*L t := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact interpolation_level K hK D hD W B weak strong f hm hf t p ht
  rw [lintegral_add_left (measurable_const.mul mh),lintegral_const_mul _ mh,lintegral_const_mul _ ml,ih,il] at levels
  refine (mul_le_mul_left' levels _).trans_eq ?_
  simp only [G,g,ofReal_norm_eq_enorm,c]
  ring

end Burnett.Analysis.SignedFourierWindow
