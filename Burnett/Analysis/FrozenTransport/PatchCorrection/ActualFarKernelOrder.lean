import Burnett.Analysis.FrozenTransport.ActualFarHighAdjoint

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric Burnett.P01 Burnett.C02 Burnett.V03
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise
open private physical_low from Burnett.Analysis.FrozenTransport.ActualV10Infrared
open private actualThinFar_zero_low from Burnett.Analysis.FrozenTransport.ActualFarHighAdjoint

private theorem actualFar_zero_lowMask (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (δ b i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (inn out : ℝ) (k j l : OrderedPair) (p q : Vec) (hq : q ≠ 0)
    (hlow : lowSlotWeight ϑ κ p q (-(p + q)) = 0) :
    actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l (p, q) = 0 := by
  have hz : ϑ (farLowArgument κ (physicalFarProfilePoint p q)) = 0 := by
    rw [physical_low hq hκ]
    exact hlow
  simp only [actualFarRadianKernel, actualThinFarCubicCorrection, farPhysicalCubicCorrection,
    cutoffGuardedFarProfile, farCutoffExtension, hz, zero_mul, Complex.ofReal_zero, mul_zero]

/-- The exact far correction is globally measurable and has order-one growth.
Its only nonzero symbols sample the prescribed compact angular window. -/
theorem actualFarKernel_measurable_orderOne (g : Mat) (a : Vec → ℝ)
    (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec)) (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (cut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) (κ : ℝ) (hκ : 0 < κ) (hs : κ < 1 / 16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ y ∈ (closedBall (0 : E) (1 / 4) ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1,
      ‖actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l y‖ ≤ M) :
    let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l
    Measurable F ∧ ∀ x : Joint, ‖F x‖ ≤ M * (1 + ‖x.1‖ + ‖x.2‖) := by
  classical
  intro F
  have low_lt (p q : E) (hq : q ≠ 0) (hL : lowSlotWeight ϑ κ p q (-(p + q)) ≠ 0) :
      ‖p‖ < (1 / 8 : ℝ) * ‖q‖ := by
    have h := lowSlotWeight_nonzero_small cut hκ hs (add_neg_cancel (p + q)) hq hL
    nlinarith [mul_lt_mul_of_pos_right hs (norm_pos_iff.mpr hq)]
  have zeroP (q : E) : F (0, q) = 0 := by simp [F, actualFarRadianKernel, actualThinFar_zero_low]
  have zeroQ (p : E) : F (p, 0) = 0 := by simp [F, actualFarRadianKernel]
  have ratioNorm (p q : E) : ‖‖q‖⁻¹ • p‖ = ‖p‖ / ‖q‖ := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q)), div_eq_inv_mul]
  let O : Set Joint := {x | x.1 ≠ 0} ∩ {x | x.2 ≠ 0} ∩ {x | ‖x.1‖ < ‖x.2‖}
  have hO : IsOpen O :=
    ((isOpen_ne_fun continuous_fst continuous_const).inter (isOpen_ne_fun continuous_snd continuous_const)).inter
      (isOpen_lt continuous_fst.norm continuous_snd.norm)
  have normMap : ContinuousOn (fun x : Joint => physicalFarProfilePoint x.1 x.2) O := by
    have ip : ContinuousOn (fun x : Joint => ‖x.1‖⁻¹) O :=
      continuous_fst.norm.continuousOn.inv₀ (fun x h => norm_ne_zero_iff.mpr h.1.1)
    have iq : ContinuousOn (fun x : Joint => ‖x.2‖⁻¹) O :=
      continuous_snd.norm.continuousOn.inv₀ (fun x h => norm_ne_zero_iff.mpr h.1.2)
    exact (ip.smul continuous_fst.continuousOn).prodMk
      ((iq.smul continuous_fst.continuousOn).prodMk (iq.smul continuous_snd.continuousOn))
  have intoDomain : MapsTo (fun x : Joint => physicalFarProfilePoint x.1 x.2) O cyclicExtensionDomain := by
    intro x hx
    have hnθ := norm_unitRep x.2 hx.1.2
    have hnω := norm_unitRep x.1 hx.1.1
    have hωn : unitRep x.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [hnω]; norm_num)
    refine ⟨hωn, ?_⟩
    change ‖‖x.2‖⁻¹ • x.1‖ < ‖unitRep x.2‖
    rw [ratioNorm, hnθ, div_lt_iff₀ (norm_pos_iff.mpr hx.1.2), one_mul]
    exact hx.2
  have hcont : ContinuousOn F O := by
    have hIR : Continuous gaugeProjectionInfrared := gaugeProjectionInfrared_contDiff.continuous
    have hI : Continuous (fun x : Joint => (gaugeProjectionInfrared (2 * ‖x.2‖) : ℂ)) :=
      Complex.continuous_ofReal.comp (hIR.comp (continuous_const.mul continuous_snd.norm))
    have hOut : Continuous (fun x : Joint => (gaugeProjectionInfrared (2 * ‖x.1 + x.2‖) : ℂ)) :=
      Complex.continuous_ofReal.comp (hIR.comp (continuous_const.mul (continuous_fst.add continuous_snd).norm))
    have hf := (actualThinFarCubicCorrection_contDiffOn g ha hϑ hκ δ b i o hm hη inn out k j l).continuousOn.comp normMap intoDomain
    exact (hI.continuousOn.mul hOut.continuousOn).mul ((Complex.continuous_ofReal.comp continuous_snd.norm).continuousOn.mul hf)
  have outside (x : Joint) (hx : x ∉ O) : F x = 0 := by
    obtain ⟨p,q⟩ := x
    by_cases hp : p = 0
    · subst p
      exact zeroP q
    by_cases hq : q = 0
    · subst q
      exact zeroQ p
    have hl : lowSlotWeight ϑ κ p q (-(p + q)) = 0 := by
      by_contra hno
      exact hx ⟨⟨hp, hq⟩, (low_lt p q hq hno).trans_le (by linarith [norm_nonneg q])⟩
    exact actualFar_zero_lowMask g a ϑ hκ δ b i o hm hη inn out k j l p q hq hl
  refine ⟨?_, ?_⟩
  · have heq : O.piecewise F (fun _ => 0) = F := by
      funext x
      by_cases hx : x ∈ O
      · simp only [Set.piecewise, if_pos hx]
      · simp only [Set.piecewise, if_neg hx, outside x hx]
    rw [← heq]
    exact hcont.measurable_piecewise continuousOn_const hO.measurableSet
  · rintro ⟨p,q⟩
    by_cases hp : p = 0
    · subst p
      rw [zeroP, norm_zero]
      positivity
    by_cases hq : q = 0
    · subst q
      rw [zeroQ, norm_zero]
      positivity
    by_cases hlow : lowSlotWeight ϑ κ p q (-(p + q)) = 0
    · rw [show F (p, q) = 0 from actualFar_zero_lowMask g a ϑ hκ δ b i o hm hη inn out k j l p q hq hlow, norm_zero]
      positivity
    let y : Joint × E := ((‖q‖⁻¹ • p, unitRep q), unitRep p)
    have ymem : y ∈ (closedBall (0 : E) (1 / 4) ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1 := by
      refine ⟨⟨mem_closedBall_zero_iff.mpr ?_, mem_sphere_zero_iff_norm.mpr (norm_unitRep q hq)⟩,
        mem_sphere_zero_iff_norm.mpr (norm_unitRep p hp)⟩
      change ‖‖q‖⁻¹ • p‖ ≤ 1 / 4
      rw [ratioNorm, div_le_iff₀ (norm_pos_iff.mpr hq)]
      linarith [low_lt p q hq hlow, norm_nonneg q]
    have window (t : ℝ) : ‖gaugeProjectionInfrared t‖ ≤ 1 := by
      rw [gaugeProjectionInfrared, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    change ‖(gaugeProjectionInfrared (2 * ‖q‖) : ℂ) * (gaugeProjectionInfrared (2 * ‖p + q‖) : ℂ) *
      ((‖q‖ : ℂ) * actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l y)‖ ≤ _
    simp only [norm_mul, Complex.norm_real, norm_norm]
    calc
      _ ≤ (1 * 1) * (‖q‖ * M) := by gcongr <;> first | exact window _ | exact hB y ymem
      _ ≤ _ := by
        simp only [one_mul, mul_comm ‖q‖ M]
        exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg p]) hM

end Burnett.V10.OriginalGaugeCompatibility
