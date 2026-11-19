import Burnett.Analysis.SignedFourierWindow.KernelLpExhaustion

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

def kernelDualPower (p : ℝ) (u : Space → ℂ) (x : Space) : ℂ :=
  conj (u x) * (‖u x‖ ^ (p-2) : ℝ)

theorem kernelDualPower_norm (p : ℝ) (hp : 2<p) (u : Space → ℂ) (x : Space) :
    ‖kernelDualPower p u x‖ = ‖u x‖ ^ (p-1) := by
  rw [kernelDualPower,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    mul_comm,←Real.rpow_add_one' (norm_nonneg _) (show p-2+1 ≠ 0 by linarith)]
  congr 1
  ring

theorem kernelDualPower_product (p : ℝ) (hp : 2<p) (u : Space → ℂ) (x : Space) :
    u x * kernelDualPower p u x = ((‖u x‖ ^ p : ℝ) : ℂ) := by
  rw [kernelDualPower,←mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq,←Complex.ofReal_mul]
  congr 1
  have r := Real.rpow_add_of_nonneg (norm_nonneg (u x)) (by norm_num : (0:ℝ)≤2) (show 0≤p-2 by linarith)
  rw [Real.rpow_two,show 2+(p-2)=p by ring] at r
  exact r.symm

theorem bounded_L1_norm_power {u : Space → ℂ} (hu : Integrable u) (M : ℝ) (hM : ∀ x, ‖u x‖ ≤ M)
    (s : ℝ) (hs : 1≤s) : Integrable (fun x => ‖u x‖ ^ s) := by
  refine (hu.norm.const_mul (M ^ (s-1))).mono' (hu.1.norm.aemeasurable.pow_const s).aestronglyMeasurable ?_
  filter_upwards with x
  change ‖‖u x‖ ^ s‖ ≤ M ^ (s-1) * ‖u x‖
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    _ = ‖u x‖ ^ (s-1) * ‖u x‖ := by
      have h := Real.rpow_add_one' (x := ‖u x‖) (y := s-1) (norm_nonneg _) (by linarith)
      simpa only [sub_add_cancel] using h
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hM x) (sub_nonneg.mpr hs)) (norm_nonneg _)

theorem kernelDualPower_norms (p : ℝ) (hp : 2<p) (u : Space → ℂ) (hm : Measurable u)
    (hi : Integrable u) (M : ℝ) (hM : ∀ x, ‖u x‖ ≤ M) :
    let P := ENNReal.ofReal p
    let Q := ENNReal.ofReal (p/(p-1))
    let h := kernelDualPower p u
    Measurable h ∧ Integrable h ∧ MemLp u P volume ∧ MemLp h Q volume ∧
      eLpNorm h Q volume = (eLpNorm u P volume)^(p-1) ∧
      ‖∫ x, u x*h x‖ₑ = (eLpNorm u P volume)^p := by
  intro P Q h
  have hpm : 0<p-1 := by linarith
  have hp0 : 0<p := by linarith
  have hq0 : 0<p/(p-1) := div_pos hp0 hpm
  have m : Measurable h := by
    change Measurable (fun x => conj (u x) * ((‖u x‖ ^ (p-2) : ℝ) : ℂ))
    fun_prop
  have ip := bounded_L1_norm_power hi M hM p (by linarith)
  have pu : MemLp u P volume := by
    apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le] using ip
  have hnorm := kernelDualPower_norm p hp u
  have ih : Integrable h := by
    apply (bounded_L1_norm_power hi M hM (p-1) (by linarith)).mono' m.aestronglyMeasurable
    exact Eventually.of_forall fun x => (hnorm x).le
  have qe : Q * ENNReal.ofReal (p-1) = P := by
    rw [←ENNReal.ofReal_mul hq0.le,div_mul_cancel₀ _ hpm.ne']
  have ev : eLpNorm h Q volume = (eLpNorm u P volume)^(p-1) := by
    calc
      _ = eLpNorm (fun x => ‖u x‖^(p-1)) Q volume := eLpNorm_congr_norm_ae <| Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hnorm x
      _ = _ := by rw [eLpNorm_norm_rpow u hpm,qe]
  refine ⟨m,ih,pu,⟨m.aestronglyMeasurable,ev.trans_lt (ENNReal.rpow_lt_top_of_nonneg hpm.le pu.2.ne)⟩,ev,?_⟩
  have intEq : (∫ x, u x*h x) = ((∫ x, ‖u x‖^p : ℝ) : ℂ) := by
    rw [←integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => kernelDualPower_product p hp u x)
  have er := eLpNorm_norm_rpow (μ := (volume : Measure Space)) (p := (1:ℝ≥0∞)) u hp0
  rw [one_mul,eLpNorm_one_eq_lintegral_enorm] at er
  rw [intEq,←ofReal_norm_eq_enorm,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ofReal_integral_eq_lintegral_ofReal ip (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  refine Eq.trans (lintegral_congr fun x => ?_) er
  rw [←ofReal_norm_eq_enorm,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
end Burnett.Analysis.SignedFourierWindow
