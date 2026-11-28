import Burnett.Analysis.TransportWard.Weyl.ScaledFrequencyDirection
import Burnett.Analysis.PrincipalEnergy.Localization.IntegratedSymbolJets

set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (contDiff_integral_of_locally_dominated_jets)
open scoped ContDiff Interval

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

private def unitSegmentTime (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem unitSegmentTime_mem (t : ℝ) : unitSegmentTime t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem unitSegmentTime_eq_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    unitSegmentTime t = t := by
  simp only [unitSegmentTime, min_eq_right ht.2, max_eq_right ht.1]

theorem linearTaylorRemainder_symbol_parameter_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) :
    ContDiff ℝ ∞ (fun z : E × P => linearTaylorRemainder (a z.2.1) z.2.2 z.1) := by
  have hx : ContDiff ℝ ∞ (fun z : E × P => z.2.1) := contDiff_fst.comp contDiff_snd
  have hξ : ContDiff ℝ ∞ (fun z : E × P => z.2.2) := contDiff_snd.comp contDiff_snd
  change ContDiff ℝ ∞ (fun z : E × P =>
    uncurry a (z.2.1,z.2.2+z.1) - uncurry a z.2 -
      frequencyDirectionalSymbol a z.1 z.2.1 z.2.2)
  exact ((ha.comp (hx.prodMk (hξ.add contDiff_fst))).sub (ha.comp contDiff_snd)).sub
    ((frequencyDirectionalSymbol_jointSmooth a ha).comp (contDiff_snd.prodMk contDiff_fst))

private def segmentDirectionalHessian (a : E → E → ℂ) (e : E) : P → ℂ :=
  uncurry (frequencyDirectionalSymbol (frequencyDirectionalSymbol a e) e)

private theorem segmentDirectionalHessian_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (e : E) :
    ContDiff ℝ ∞ (segmentDirectionalHessian a e) :=
  frequencyDirectionalSymbol_smooth _ (frequencyDirectionalSymbol_smooth a ha e) e

private theorem segmentDirectionalHessian_joint_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : E, ∀ p : P,
      ‖iteratedFDeriv ℝ n (segmentDirectionalHessian a e) p‖ * W p.2 ≤ C * ‖e‖^2 := by
  obtain ⟨C,hC,hB⟩ := ha.bound (n+1+1)
  refine ⟨C,hC,fun e p => ?_⟩
  let a₁ := frequencyDirectionalSymbol a e
  let a₂ := frequencyDirectionalSymbol a₁ e
  let J (f : E → E → ℂ) (k : ℕ) := ‖radianScaledParameterJet (uncurry f) k p‖
  have h₁ : W p.2 * J a₂ n ≤ ‖e‖ * J a₁ (n+1) :=
    scaled_frequencyDirectionalSymbol_le a₁ (frequencyDirectionalSymbol_smooth a ha.smooth e) e n p
  have h₂ : W p.2 * J a₁ (n+1) ≤ ‖e‖ * J a (n+1+1) :=
    scaled_frequencyDirectionalSymbol_le a ha.smooth e (n+1) p
  have hw := radian_frequency_weight_pos p.2
  have hUnscaled : ‖iteratedFDeriv ℝ n (segmentDirectionalHessian a e) p‖ ≤ J a₂ n :=
    radian_parameter_jet_norm_le_scaled _ n p
  apply (mul_le_mul_iff_left₀ hw).mp
  calc
    _ ≤ (J a₂ n * W p.2) * W p.2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUnscaled hw.le) hw.le
    _ = (W p.2 * J a₂ n) * W p.2 := by ring
    _ ≤ (‖e‖ * J a₁ (n+1)) * W p.2 := mul_le_mul_of_nonneg_right h₁ hw.le
    _ = ‖e‖ * (W p.2 * J a₁ (n+1)) := by ring
    _ ≤ ‖e‖ * (‖e‖ * J a (n+1+1)) := mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
    _ ≤ ‖e‖ * (‖e‖ * (C * W p.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB p) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private def segmentDirectionalHessianIntegrand (a : E → E → ℂ) (e : E)
    (t : ℝ) (p : P) : ℂ :=
  (1-unitSegmentTime t) • segmentDirectionalHessian a e (p+((0 : E),unitSegmentTime t • e))

private theorem segmentDirectionalHessianIntegrand_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (e : E) (t : ℝ) :
    ContDiff ℝ ∞ (segmentDirectionalHessianIntegrand a e t) :=
  ((segmentDirectionalHessian_smooth ha e).comp (contDiff_id.add contDiff_const)).const_smul _

private theorem iteratedFDeriv_segmentDirectionalHessianIntegrand {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (e : E) (n : ℕ) (t : ℝ) (p : P) :
    iteratedFDeriv ℝ n (segmentDirectionalHessianIntegrand a e t) p =
      (1-unitSegmentTime t) • iteratedFDeriv ℝ n (segmentDirectionalHessian a e)
        (p+((0 : E),unitSegmentTime t • e)) := by
  have hs : ContDiff ℝ ∞ (fun q : P => segmentDirectionalHessian a e
      (q+((0 : E),unitSegmentTime t • e))) :=
    (segmentDirectionalHessian_smooth ha e).comp (contDiff_id.add contDiff_const)
  change iteratedFDeriv ℝ n ((1-unitSegmentTime t) • (fun q : P =>
    segmentDirectionalHessian a e (q+((0 : E),unitSegmentTime t • e)))) p = _
  rw [iteratedFDeriv_const_smul_apply
    (hs.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))), iteratedFDeriv_comp_add_right]

private theorem segmentDirectionalHessianIntegrand_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : E) (t : ℝ) (p : P),
      ‖iteratedFDeriv ℝ n (segmentDirectionalHessianIntegrand a e t) p‖ ≤
        C * (W e)^3 / W p.2 := by
  obtain ⟨C,hC,hB⟩ := segmentDirectionalHessian_joint_order_minus_one ha n
  refine ⟨C,hC,fun e t p => ?_⟩
  let q := p+((0 : E),unitSegmentTime t • e)
  let v := ‖iteratedFDeriv ℝ n (segmentDirectionalHessian a e) q‖
  have hGap : ‖p.2-q.2‖ ≤ ‖e‖ := by
    change ‖p.2-(p.2+unitSegmentTime t • e)‖ ≤ _
    rw [show p.2-(p.2+unitSegmentTime t • e) = -(unitSegmentTime t • e) by abel,
      norm_neg,norm_smul,Real.norm_of_nonneg (unitSegmentTime_mem t).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (unitSegmentTime_mem t).2
  have hW : W p.2 ≤ W e * W q.2 :=
    (radian_frequency_weight_shift_le p.2 q.2).trans
      (mul_le_mul_of_nonneg_right (add_le_add_left hGap 1) (radian_frequency_weight_pos q.2).le)
  have hε : 0 ≤ 1-unitSegmentTime t := sub_nonneg.mpr (unitSegmentTime_mem t).2
  have hp := radian_frequency_weight_pos p.2
  rw [iteratedFDeriv_segmentDirectionalHessianIntegrand ha.smooth,norm_smul,Real.norm_of_nonneg hε]
  change (1-unitSegmentTime t)*v ≤ _
  apply (le_div_iff₀ hp).mpr
  calc
    _ ≤ v * W p.2 := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (by linarith [(unitSegmentTime_mem t).1])) hp.le
    _ ≤ v * (W e * W q.2) := mul_le_mul_of_nonneg_left hW (norm_nonneg _)
    _ = (v * W q.2) * W e := by ring
    _ ≤ (C * ‖e‖^2) * W e := mul_le_mul_of_nonneg_right (hB e q) (radian_frequency_weight_pos e).le
    _ ≤ (C * (W e)^2) * W e := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 2) hC)
      (radian_frequency_weight_pos e).le
    _ = _ := by ring

/-- All joint jets of the genuine frequency Taylor remainder retain the
inverse original frequency weight. The shifted frequency costs only the
cubic Schwartz moment of the modulation variable. -/
theorem linearTaylorRemainder_symbol_joint_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : E, ∀ p : P,
      ‖iteratedFDeriv ℝ n (fun q : P => linearTaylorRemainder (a q.1) q.2 e) p‖ ≤
        C * (W e)^3 / W p.2 := by
  let I := Ioc (0 : ℝ) 1
  let μ := (volume : Measure ℝ).restrict I
  have hMeasure : μ.real univ = 1 := by
    rw [show μ = (volume : Measure ℝ).restrict I from rfl, measureReal_restrict_apply_univ]
    simp [I, measureReal_def, Real.volume_Ioc]
  obtain ⟨C,hC,hB⟩ := segmentDirectionalHessianIntegrand_order_minus_one ha n
  refine ⟨C,hC,fun e p => ?_⟩
  let F := segmentDirectionalHessianIntegrand a e
  have hDerivative (k : ℕ) (q : P) :
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (F t) q) μ := by
    apply Continuous.aestronglyMeasurable
    simp_rw [show F = segmentDirectionalHessianIntegrand a e from rfl,
      iteratedFDeriv_segmentDirectionalHessianIntegrand ha.smooth]
    have hc : Continuous unitSegmentTime := continuous_const.max (continuous_const.min continuous_id)
    have hd := (segmentDirectionalHessian_smooth ha.smooth e).continuous_iteratedFDeriv
      (m := k) (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    exact (continuous_const.sub hc).smul (hd.comp
      (continuous_const.add (continuous_const.prodMk (hc.smul continuous_const))))
  have hEq : (fun q : P => linearTaylorRemainder (a q.1) q.2 e) = fun q => ∫ t, F t q ∂μ := by
    funext q
    have haSlice : ContDiff ℝ ∞ (a q.1) := ha.smooth.comp (contDiff_const.prodMk contDiff_id)
    rw [linearTaylorRemainder_eq_integral (a q.1) isOpen_univ haSlice.contDiffOn q.2 e
      (fun _ _ => mem_univ _), intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    rw [secondFDeriv_eq_frequencyDirectionalSymbol_twice a ha.smooth]
    simp only [F,segmentDirectionalHessianIntegrand,unitSegmentTime_eq_of_mem (Ioc_subset_Icc_self ht)]
    change (1-t) • frequencyDirectionalSymbol (frequencyDirectionalSymbol a e) e q.1
      (q.2+t • e) = (1-t) • frequencyDirectionalSymbol (frequencyDirectionalSymbol a e) e
        (q.1+0) (q.2+t • e)
    rw [add_zero]
  have hDom (k : ℕ) (q : P) : ∃ B : ℝ → ℝ, Integrable B μ ∧
      ∀ t y, y ∈ Metric.ball q 1 → ‖iteratedFDeriv ℝ k (F t) y‖ ≤ B t := by
    obtain ⟨D,hD,hU⟩ := segmentDirectionalHessianIntegrand_order_minus_one ha k
    refine ⟨fun _ => D * (W e)^3, ?_, fun t y _ => (hU e t y).trans ?_⟩
    · exact integrableOn_const (by simp [I, Real.volume_Ioc])
    · exact div_le_self (mul_nonneg hD (pow_nonneg (radian_frequency_weight_pos e).le _))
        (radian_frequency_weight_one_le y.2)
  have hJets := (contDiff_integral_of_locally_dominated_jets μ F
    (segmentDirectionalHessianIntegrand_smooth ha.smooth e) hDerivative hDom).2
  rw [hEq, hJets]
  have hi : Integrable (fun _ : ℝ => C * (W e)^3 / W p.2) μ :=
    integrableOn_const (by simp [I, Real.volume_Ioc])
  calc
    _ ≤ ∫ _ : ℝ, C * (W e)^3 / W p.2 ∂μ :=
      norm_integral_le_of_norm_le hi (.of_forall fun t => hB e t p)
    _ = _ := by rw [integral_const,hMeasure,one_smul]

end Burnett.V03
