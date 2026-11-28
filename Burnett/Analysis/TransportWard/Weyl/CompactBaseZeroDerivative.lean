import Burnett.Analysis.TransportWard.Weyl.BaseDerivativeBounds
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2000

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Filter MeasureTheory Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.CarlesonEmbedding (baseDirectionSymbol_joint_smooth firstOrderAction_contDiff_of_pureBaseOrder)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff FourierTransform Topology

open private leftPhase leftPhaseRate leftPhase_norm leftPhase_continuous
  leftPhaseRate_continuous leftPhaseRate_norm_le leftPhase_line_hasDerivAt
  firstOrderAction_eq_integral from Burnett.Analysis.PrincipalEnergy.Quantization.ActualDerivative

local notation "W" => radianFrequencyWeight

private theorem firstOrderAction_baseDerivative_of_orderZero
    {b : E → E → ℂ} (hs : ContDiff ℝ ∞ (uncurry b))
    (hb : BaseDerivativeBounds b (fun _ => 1)) (f : SchwartzMap E ℂ) (x e : E) :
    HasDerivAt (fun t : ℝ => firstOrderAction b f (x + t • e))
      (firstOrderAction (baseDirectionSymbol b e) f x +
        firstOrderAction b (SchwartzMap.pderivCLM ℂ e f) x) 0 := by
  obtain ⟨M, hM, hMbound⟩ := hb.bound 0
  obtain ⟨D, hD, hDbound⟩ := hb.bound 1
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let Q := baseDirectionSymbol b e
  let L (t : ℝ) (ξ : E) := leftPhase (x + t • e) ξ * (b (x + t • e) ξ * F ξ)
  let L' (t : ℝ) (ξ : E) :=
    leftPhase (x + t • e) ξ *
      ((Q (x + t • e) ξ + leftPhaseRate e ξ * b (x + t • e) ξ) * F ξ)
  let bound (ξ : E) := (D * ‖e‖ + (2 * Real.pi * ‖e‖) * M) * (W ξ * ‖F ξ‖)
  have hB (y ξ : E) : ‖b y ξ‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero, mul_one] using hMbound y ξ
  have hQ (y ξ : E) : ‖Q y ξ‖ ≤ D * ‖e‖ := by
    have hd := hDbound y ξ
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero, mul_one] at hd
    exact (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have hCont (y : E) : Continuous (b y) := hs.continuous.comp (continuous_const.prodMk continuous_id)
  have hQCont (y : E) : Continuous (Q y) :=
    (baseDirectionSymbol_joint_smooth hs e).continuous.comp (continuous_const.prodMk continuous_id)
  have hIntL (t : ℝ) : Integrable (L t) volume := by
    refine (F.integrable.norm.const_mul M).mono'
      (((leftPhase_continuous _).mul ((hCont _).mul F.continuous))).aestronglyMeasurable ?_
    filter_upwards with ξ
    simp only [L,norm_mul,leftPhase_norm,one_mul]
    exact mul_le_mul_of_nonneg_right (hB _ ξ) (norm_nonneg _)
  have hMeas : AEStronglyMeasurable (L' 0) volume := by
    exact ((leftPhase_continuous _).mul
      (((hQCont _).add ((leftPhaseRate_continuous _).mul (hCont _))).mul F.continuous)).aestronglyMeasurable
  have hDerivative (t : ℝ) (ξ : E) : HasDerivAt (fun s => L s ξ) (L' t ξ) t := by
    have hLine : HasDerivAt (fun s : ℝ => x + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have hSymbol := ((hb.smooth ξ).differentiable (by simp) (x + t • e)).hasFDerivAt.comp_hasDerivAt t hLine
    convert (leftPhase_line_hasDerivAt x e ξ t).mul (hSymbol.mul_const (F ξ)) using 1
    simp only [L',Q,baseDirectionSymbol,Function.comp_apply]
    ring
  have hBound (t : ℝ) (ξ : E) : ‖L' t ξ‖ ≤ bound ξ := by
    let y := x + t • e
    have hW : 1 ≤ W ξ := le_add_of_nonneg_right (norm_nonneg _)
    simp only [L',norm_mul,leftPhase_norm,one_mul,bound]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖Q y ξ‖ + ‖leftPhaseRate e ξ * b y ξ‖ := norm_add_le _ _
      _ ≤ (D * ‖e‖) * W ξ + ((2 * Real.pi * ‖e‖) * W ξ) * M :=
        add_le_add ((hQ y ξ).trans (le_mul_of_one_le_right (mul_nonneg hD (norm_nonneg _)) hW))
          (by
            rw [norm_mul]
            exact mul_le_mul (leftPhaseRate_norm_le e ξ) (hB y ξ) (norm_nonneg _)
              (mul_nonneg (by positivity) (zero_le_one.trans hW)))
      _ = (D * ‖e‖ + (2 * Real.pi * ‖e‖) * M) * W ξ := by
        generalize W ξ = w
        ring
  have hMoment : Integrable (fun ξ => W ξ * ‖F ξ‖) (volume : Measure E) := by
    apply (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)).congr
    filter_upwards with ξ
    simp only [Pi.add_apply,radianFrequencyWeight,pow_one,add_mul,one_mul]
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := L) (F' := L') (x₀ := 0) (μ := (volume : Measure E)) (ε := 1)
    (by norm_num) (.of_forall fun t => (hIntL t).aestronglyMeasurable) (hIntL 0)
    hMeas (.of_forall fun ξ t _ => hBound t ξ) (hMoment.const_mul _)
    (.of_forall fun ξ t _ => hDerivative t ξ)).2
  have hForm : (fun t : ℝ => ∫ ξ, L t ξ) = fun t => firstOrderAction b f (x + t • e) := by
    funext t
    rw [firstOrderAction_eq_integral]
    rfl
  rw [hForm] at h
  convert h using 1
  let g := SchwartzMap.pderivCLM ℂ e f
  have hFourier (ξ : E) : (𝓕 (g : E → ℂ)) ξ = leftPhaseRate e ξ * (𝓕 (f : E → ℂ)) ξ := by
    rw [show (𝓕 (g : E → ℂ)) ξ = _ from Burnett.Analysis.HminusWeightedDual.fourier_pderiv f e ξ]
    unfold leftPhaseRate
    push_cast
    ring
  have hIntQ : Integrable (fun ξ => leftPhase x ξ * (Q x ξ * F ξ)) volume :=
    (F.integrable.norm.const_mul (D * ‖e‖)).mono'
      ((leftPhase_continuous _).mul ((hQCont x).mul F.continuous)).aestronglyMeasurable
      (.of_forall fun ξ => by
        rw [norm_mul,leftPhase_norm,one_mul,norm_mul]
        exact mul_le_mul_of_nonneg_right (hQ x ξ) (norm_nonneg _))
  let G := SchwartzMap.fourierTransformCLM ℂ g
  have hIntG : Integrable (fun ξ => leftPhase x ξ * (b x ξ * G ξ)) volume :=
    (G.integrable.norm.const_mul M).mono'
      ((leftPhase_continuous _).mul ((hCont x).mul G.continuous)).aestronglyMeasurable
      (.of_forall fun ξ => by
        rw [norm_mul,leftPhase_norm,one_mul,norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x ξ) (norm_nonneg _))
  rw [firstOrderAction_eq_integral _ f x,firstOrderAction_eq_integral _ g x]
  change (∫ ξ : E, leftPhase x ξ * (Q x ξ * F ξ)) +
    (∫ ξ : E, leftPhase x ξ * (b x ξ * G ξ)) = _
  rw [← integral_add hIntQ hIntG]
  apply integral_congr_ae
  refine .of_forall fun ξ => ?_
  simp only [L',zero_smul,add_zero]
  change leftPhase x ξ * (Q x ξ * F ξ) +
    leftPhase x ξ * (b x ξ * (𝓕 (g : E → ℂ)) ξ) = _
  rw [hFourier]
  change leftPhase x ξ * (Q x ξ * F ξ) +
    leftPhase x ξ * (b x ξ * (leftPhaseRate e ξ * F ξ)) =
      leftPhase x ξ * ((Q x ξ + leftPhaseRate e ξ * b x ξ) * F ξ)
  ring

/-- Differentiating a compact zero-order left action requires only pure
spatial seminorms and joint continuity, with the exact right derivative. -/
theorem physicalCoordinatePartial_leftAction_of_orderZero {b : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry b)) (hb : BaseDerivativeBounds b (fun _ => 1))
    (j : Fin 4) (f : SchwartzMap E ℂ) (x : E) :
    physicalCoordinatePartial j (firstOrderAction b f) x =
      firstOrderAction (baseDirectionSymbol b (coordinateDirection j)) f x +
        firstOrderAction b (frozenSchwartzCoordinatePartial j f) x := by
  have hBounds (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ,
      ‖iteratedFDeriv ℝ n (fun z => b z ξ) y‖ ≤ C * (1 + ‖ξ‖) := by
    obtain ⟨C,hC,h⟩ := hb.bound n
    exact ⟨C,hC,fun y ξ => (h y ξ).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hC)⟩
  have hd := ((firstOrderAction_contDiff_of_pureBaseOrder hs hBounds f).differentiable
    (by simp) x).hasFDerivAt
  have hLine : HasDerivAt (fun t : ℝ => x + t • coordinateDirection j) (coordinateDirection j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateDirection j)).const_add x
  have hD : HasFDerivAt (firstOrderAction b f) (fderiv ℝ (firstOrderAction b f) x)
      ((fun t : ℝ => x + t • coordinateDirection j) 0) := by
    simpa only [zero_smul,add_zero] using hd
  have hComp := hD.comp_hasDerivAt (0 : ℝ) hLine
  have hComp' : HasDerivAt (fun t : ℝ => firstOrderAction b f (x + t • coordinateDirection j))
      (physicalCoordinatePartial j (firstOrderAction b f) x) 0 := by
    simpa only [zero_smul,add_zero,physicalCoordinatePartial,Function.comp_apply] using hComp
  exact hComp'.unique (firstOrderAction_baseDerivative_of_orderZero hs hb f x (coordinateDirection j))

end Burnett.V03
