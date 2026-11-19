import Burnett.Analysis.CenteredMaximal.MaximalDistribution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set
open scoped ENNReal

/-- The contribution below the truncation height in Marcinkiewicz interpolation.
The infinite height integral converges precisely on the side p<2 used here. -/
theorem integrated_lower_square (g : Space → ℝ) (hm : Measurable g) (hn : ∀ x, 0 ≤ g x) (p : ℝ)
    (hp : 1<p) (hp2 : p<2) :
    (∫⁻ t in Ioi (0:ℝ), (∫⁻ x in {x : Space | g x ≤ t}, (ENNReal.ofReal (g x))^2) *
      ENNReal.ofReal (t^(p-3))) =
      ENNReal.ofReal (2-p)⁻¹ * ∫⁻ x, (ENNReal.ofReal (g x))^p := by
  classical
  let v := fun t : ℝ => ENNReal.ofReal (t^(p-3))
  let Q := fun x : Space => (ENNReal.ofReal (g x))^2
  let F := fun t x => if g x ≤ t then Q x * v t else 0
  have mf : Measurable (Function.uncurry F) := by
    change Measurable (fun z : ℝ × Space => if g z.2 ≤ z.1 then Q z.2*v z.1 else 0)
    apply Measurable.ite (measurableSet_le (hm.comp measurable_snd) measurable_fst)
    · dsimp only [Q,v]; fun_prop
    · exact measurable_const
  have inside (t : ℝ) : (∫⁻ x in {x : Space | g x ≤ t}, Q x) * v t = ∫⁻ x, F t x := by
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,← lintegral_indicator (measurableSet_le hm measurable_const)]
    rfl
  have column (x : Space) : (∫⁻ t in Ioi (0:ℝ), F t x) =
      ENNReal.ofReal (2-p)⁻¹ * (ENNReal.ofReal (g x))^p := by
    rcases (hn x).eq_or_lt with hx|hx
    · simp [F,Q,← hx,ENNReal.zero_rpow_of_pos (by linarith : 0<p)]
    have hset : (Ici (g x)) ∩ Ioi 0 = Ici (g x) := inter_eq_left.mpr (fun t ht => hx.trans_le ht)
    have he (t : ℝ) : F t x = (Ici (g x)).indicator (fun t => Q x * v t) t := rfl
    simp_rw [he]
    rw [lintegral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,hset,
      ← restrict_Ioi_eq_restrict_Ici,lintegral_const_mul' _ _ (by dsimp [Q]; finiteness)]
    have fint := integrableOn_Ioi_rpow_of_lt (by linarith : p-3 < -1) hx
    have pos : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi (g x))] (fun t : ℝ => t^(p-3)) := by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hx.trans ht).le _
    change (ENNReal.ofReal (g x))^2 * (∫⁻ t in Ioi (g x), ENNReal.ofReal (t^(p-3))) = _
    rw [← ofReal_integral_eq_lintegral_ofReal fint pos,integral_Ioi_rpow_of_lt (by linarith) hx,
      show p-3+1=p-2 by ring,ENNReal.ofReal_rpow_of_nonneg hx.le (by linarith : 0≤p),
      ← ENNReal.ofReal_pow hx.le,← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]
    congr 1
    have hpow : (g x)^2 * (g x)^(p-2) = (g x)^p := by
      rw [← Real.rpow_two,← Real.rpow_add hx]; ring_nf
    field_simp [ne_of_lt (sub_neg.mpr hp2),(sub_pos.mpr hp2).ne']
    nlinarith [hpow]
  change (∫⁻ t in Ioi (0:ℝ), (∫⁻ x in {x : Space | g x ≤ t}, Q x)*v t) = _
  simp_rw [inside]
  rw [lintegral_lintegral_swap mf.aemeasurable]
  simp_rw [column]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Burnett.Analysis.SignedFourierWindow
