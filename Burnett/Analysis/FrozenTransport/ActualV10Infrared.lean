import Burnett.Analysis.FrozenTransport.ActualThinFarCubicProfile
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

set_option autoImplicit false
set_option maxHeartbeats 4800000
noncomputable section
namespace Burnett.V10.OriginalGaugeCompatibility
open Set Metric Burnett.P01 Burnett.C02 Burnett.V03
open Burnett.A02.FrequencySplit (E radianFourier)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped RealInnerProductSpace Matrix.Norms.Elementwise

private theorem physical_low {p q : Vec} (hq : q≠0) {κ : ℝ} (hκ : 0<κ) :
    farLowArgument κ (physicalFarProfilePoint p q) = ‖p‖^2 / (κ^2*(‖q‖^2+‖-(p+q)‖^2)) := by
  let x := physicalFarProfilePoint p q
  have eq : farHighOutput x = ‖q‖⁻¹ • (p+q) := by simp only [x,farHighOutput,physicalFarProfilePoint,unitRep,smul_add,add_comm]
  change farLowArgument κ x = _
  rw [farLowArgument,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,eq,norm_neg]
  change ‖‖q‖⁻¹ • p‖^2 / (κ^2*(1+‖‖q‖⁻¹ • (p+q)‖^2)) = _
  simp only [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q))]
  have pos : 0<‖q‖^2+‖p+q‖^2 := add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hq) _) (sq_nonneg _)
  field_simp [hκ.ne',norm_ne_zero_iff.mpr hq,pos.ne']

/-- For the original physical low field, both true high radial windows
are exactly one on the active physical far quotient. Equality is pointwise
even on an axis and before either high amplitude is tested. -/
theorem actualThinFar_dual_infrared (g : Mat) (a : Vec → ℝ) (θ : ℝ → ℝ)
    (cut : ∀ s : ℝ, 1≤s → θ s=0) (κ : ℝ) (hκ : 0<κ) (hs : κ<1/16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0<η) (inn out : ℝ)
    (k j l : OrderedPair) (z : ProjectionSchwartzMatrix) (p q : Vec) :
    let H := radianFourier (projectionFullSchwartz z k.1 k.2) p
    let B := (‖q‖ : ℂ) * actualThinFarCubicCorrection g a θ κ δ b i o hm hη inn out k j l (physicalFarProfilePoint p q)
    (gaugeProjectionInfrared (2*‖q‖) : ℂ)*(gaugeProjectionInfrared (2*‖p+q‖) : ℂ)*B*H=B*H := by
  intro H B
  by_cases hp : ‖p‖ ≤ 1
  · have h : H=0 := by simp [H,projectionFullSchwartz_radianFourier,regularizedComplexGaugeProjection,gaugeProjectionInfrared_zero hp]
    simp [h]
  by_cases hq : q=0
  · subst q; simp [B]
  by_cases hmask : lowSlotWeight θ κ p q (-(p+q))=0
  · have low : θ (farLowArgument κ (physicalFarProfilePoint p q))=0 := by rw [physical_low hq hκ]; exact hmask
    have bz : B=0 := by simp only [B,actualThinFarCubicCorrection,farPhysicalCubicCorrection,cutoffGuardedFarProfile,farCutoffExtension,low,zero_mul,Complex.ofReal_zero,mul_zero]
    simp [bz]
  have near := lowSlotWeight_nonzero_small cut hκ hs (add_neg_cancel (p+q)) hq hmask
  have strict := mul_lt_mul_of_pos_right hs (norm_pos_iff.mpr hq)
  have tri : ‖q‖ ≤ ‖p+q‖+‖p‖ := by simpa only [add_sub_cancel_left] using norm_sub_le (p+q) p
  have nq : 2≤2*‖q‖ := by linarith
  have nr : 2≤2*‖p+q‖ := by linarith
  simp only [gaugeProjectionInfrared_one nq,gaugeProjectionInfrared_one nr,Complex.ofReal_one,one_mul]

end Burnett.V10.OriginalGaugeCompatibility
