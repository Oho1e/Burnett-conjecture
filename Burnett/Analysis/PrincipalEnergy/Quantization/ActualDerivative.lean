import Burnett.Analysis.PrincipalEnergy.Quantization.BaseDerivative
import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit
import Burnett.Analysis.H1FourierEnergy
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology

/-- The full left quantization in the mathlib Fourier convention. -/
def firstOrderAction (a : E → E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  𝓕⁻ (fun ξ => a x ξ * (𝓕 f) ξ) x

def baseDirectionSymbol (a : E → E → ℂ) (e x ξ : E) : ℂ :=
  fderiv ℝ (fun y => a y ξ) x e

private theorem baseSection_differentiableAt {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (x ξ : E) :
    DifferentiableAt ℝ (fun y => a y ξ) x := by
  let L := (continuousMultilinearCurryFin0 ℝ E ℂ).toLinearIsometry.toContinuousLinearMap
  let B := fun y => iteratedFDeriv ℝ 0 (a y) ξ
  have heq : (fun y => a y ξ) = L ∘ B := by funext y; rfl
  rw [heq]
  exact L.differentiableAt.comp x (ha.baseDiff 0 ξ).differentiableAt

private theorem baseDirectionSymbol_grow {a : E → E → ℂ} {D : ℝ}
    (ha : FirstBaseFrequencyOrderOne a) (hD : ∀ x ξ,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ 0 (a y) ξ) x‖ ≤ D * (1 + ‖ξ‖)) (x e ξ : E) :
    ‖baseDirectionSymbol a e x ξ‖ ≤ D * ‖e‖ * (1 + ‖ξ‖) := by
  let L := (continuousMultilinearCurryFin0 ℝ E ℂ).toLinearIsometry.toContinuousLinearMap
  let B := fun y => iteratedFDeriv ℝ 0 (a y) ξ
  have heq : (fun y => a y ξ) = L ∘ B := by funext y; rfl
  have hd : DifferentiableAt ℝ B x := (ha.baseDiff 0 ξ).differentiableAt
  rw [baseDirectionSymbol, heq, (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
  change ‖(continuousMultilinearCurryFin0 ℝ E ℂ) (fderiv ℝ B x e)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ e).trans
    ((mul_le_mul_of_nonneg_right (hD x ξ) (norm_nonneg _)).trans_eq (by ring))

private def leftPhase (x ξ : E) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)

private def leftPhaseRate (e ξ : E) : ℂ :=
  (↑(2 * Real.pi * inner ℝ ξ e) : ℂ) * Complex.I

private theorem leftPhase_norm (x ξ : E) : ‖leftPhase x ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem leftPhase_continuous (x : E) : Continuous (leftPhase x) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const)

private theorem leftPhaseRate_continuous (e : E) : Continuous (leftPhaseRate e) :=
  (Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const

private theorem leftPhaseRate_norm_le (e ξ : E) :
    ‖leftPhaseRate e ξ‖ ≤ (2 * Real.pi * ‖e‖) * (1 + ‖ξ‖) := by
  rw [leftPhaseRate, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  calc
    _ ≤ (2 * Real.pi) * (‖ξ‖ * ‖e‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ = (2 * Real.pi * ‖e‖) * ‖ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem leftPhase_line_hasDerivAt (x e ξ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => leftPhase (x + s • e) ξ)
      (leftPhase (x + t • e) ξ * leftPhaseRate e ξ) t := by
  have hAffine : HasDerivAt (fun s : ℝ => inner ℝ ξ x + s * inner ℝ ξ e) (inner ℝ ξ e) t := by
    simpa using ((hasDerivAt_id t).mul_const (inner ℝ ξ e)).const_add (inner ℝ ξ x)
  have h := ((hAffine.const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [leftPhase, leftPhaseRate, inner_add_right, real_inner_smul_right] using h

private theorem firstOrderAction_eq_integral (a : E → E → ℂ) (f : E → ℂ) (x : E) :
    firstOrderAction a f x = ∫ ξ, leftPhase x ξ * (a x ξ * (𝓕 f) ξ) := by
  rw [firstOrderAction, Real.fourierIntegralInv_eq']
  rfl

private theorem integrable_schwartz_quadratic_moment (F : SchwartzMap E ℂ) :
    Integrable (fun ξ : E => (1 + ‖ξ‖) ^ 2 * ‖F ξ‖) := by
  have hLinear := (F.integrable_pow_mul (volume : Measure E) 1).const_mul 2
  have hQuadratic := F.integrable_pow_mul (volume : Measure E) 2
  apply ((F.integrable.norm.add hLinear).add hQuadratic).congr
  filter_upwards with ξ
  simp only [Pi.add_apply, pow_one]
  ring

/-- Actual derivative under the full left-quantization integral on a Schwartz
input. The displayed integral is in the same Fourier convention and uses the
same symbol and original input. -/
theorem firstOrderAction_line_hasDerivAt {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hBase : ∀ x e, Continuous (baseDirectionSymbol a e x))
    (f : SchwartzMap E ℂ) (x e : E) :
    HasDerivAt (fun t : ℝ => firstOrderAction a f (x + t • e))
      (∫ ξ, leftPhase x ξ *
        ((baseDirectionSymbol a e x ξ + leftPhaseRate e ξ * a x ξ) * (𝓕 (f : E → ℂ)) ξ))
      0 := by
  obtain ⟨M,hM,hGrow⟩ := ha.frequency.order 0
  obtain ⟨D,hD,hGrowBase⟩ := ha.order 0
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let k (t : ℝ) (ξ : E) := leftPhase (x + t • e) ξ * (a (x + t • e) ξ * F ξ)
  let k' (t : ℝ) (ξ : E) := leftPhase (x + t • e) ξ *
    ((baseDirectionSymbol a e (x + t • e) ξ + leftPhaseRate e ξ * a (x + t • e) ξ) * F ξ)
  let W (ξ : E) : ℝ := 1 + ‖ξ‖
  have hW (ξ : E) : 1 ≤ W ξ := le_add_of_nonneg_right (norm_nonneg ξ)
  let bound (ξ : E) := ((2 * Real.pi * ‖e‖) * M + D * ‖e‖) * (W ξ ^ 2 * ‖F ξ‖)
  have hF_int (t : ℝ) : Integrable (k t) := by
    apply ((F.integrable.norm.add
      (F.integrable_pow_mul (volume : Measure E) 1)).const_mul M).mono'
      ((leftPhase_continuous _).mul ((ha.frequency.smooth _).continuous.mul
        F.continuous)).aestronglyMeasurable
    filter_upwards with ξ
    change ‖leftPhase (x + t • e) ξ * (a (x + t • e) ξ * F ξ)‖ ≤ _
    rw [norm_mul, leftPhase_norm, one_mul, norm_mul]
    have hA : ‖a (x + t • e) ξ‖ ≤ M * W ξ := by
      simpa only [W, pow_zero, norm_iteratedFDeriv_zero, mul_one] using hGrow (x + t • e) ξ
    calc
      _ ≤ (M * W ξ) * ‖F ξ‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = _ := by simp only [W, Pi.add_apply, pow_one]; ring
  have hdiff (t : ℝ) (ξ : E) : HasDerivAt (fun s => k s ξ) (k' t ξ) t := by
    have hLine : HasDerivAt (fun s : ℝ => x + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have hSymbol := (baseSection_differentiableAt ha (x + t • e) ξ).hasFDerivAt.comp_hasDerivAt t hLine
    convert (leftPhase_line_hasDerivAt x e ξ t).mul (hSymbol.mul_const (F ξ)) using 1
    simp only [k', baseDirectionSymbol, Function.comp_apply]
    ring
  have hst (y ξ : E) : ‖baseDirectionSymbol a e y ξ‖ ≤ D * ‖e‖ * W ξ := by
    exact baseDirectionSymbol_grow ha (fun y ξ => by simpa only [pow_zero, mul_one] using hGrowBase y ξ)
      y e ξ
  have hk' (t : ℝ) (ξ : E) : ‖k' t ξ‖ ≤ bound ξ := by
    let y := x + t • e
    have hA : ‖a y ξ‖ ≤ M * W ξ := by
      simpa only [W, pow_zero, norm_iteratedFDeriv_zero, mul_one] using hGrow y ξ
    have hWnon := zero_le_one.trans (hW ξ)
    have hSquare : W ξ ≤ W ξ ^ 2 := by
      simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right (hW ξ) hWnon
    have hRate := leftPhaseRate_norm_le e ξ
    dsimp only [k']
    rw [norm_mul, leftPhase_norm, one_mul, norm_mul]
    change _ ≤ ((2 * Real.pi * ‖e‖) * M + D * ‖e‖) * (W ξ ^ 2 * ‖F ξ‖)
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖baseDirectionSymbol a e y ξ‖ + ‖leftPhaseRate e ξ * a y ξ‖ := norm_add_le _ _
      _ ≤ D * ‖e‖ * W ξ + ((2 * Real.pi * ‖e‖) * W ξ) * (M * W ξ) :=
        add_le_add (hst y ξ) (by
          rw [norm_mul]
          exact mul_le_mul hRate hA (norm_nonneg _) (by positivity))
      _ ≤ D * ‖e‖ * W ξ ^ 2 + ((2 * Real.pi * ‖e‖) * W ξ) * (M * W ξ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hSquare (by positivity)) _
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (k' 0) := by
    exact ((leftPhase_continuous _).mul
      (((hBase _ _).add ((leftPhaseRate_continuous _).mul
        (ha.frequency.smooth _).continuous)).mul F.continuous)).aestronglyMeasurable
  have hBoundInt : Integrable bound := (integrable_schwartz_quadratic_moment F).const_mul _
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := k) (F' := k') (x₀ := 0) (μ := (volume : Measure E)) (ε := 1)
    (by norm_num) (Eventually.of_forall fun t => (hF_int t).aestronglyMeasurable) (hF_int 0)
    hmeas (Eventually.of_forall fun ξ t _ => hk' t ξ) hBoundInt
    (Eventually.of_forall fun ξ t _ => hdiff t ξ)).2
  simp only [firstOrderAction_eq_integral, k, k', zero_smul, add_zero, F] at h ⊢
  exact h

private theorem integrable_phase_symbol {b : E → ℂ} (hb : Continuous b)
    {M : ℝ} (hM : ∀ ξ, ‖b ξ‖ ≤ M * (1 + ‖ξ‖)) (f : SchwartzMap E ℂ) (x : E) :
    Integrable (fun ξ => leftPhase x ξ * (b ξ * (𝓕 (f : E → ℂ)) ξ)) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  refine ((F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)).const_mul M).mono'
    ((leftPhase_continuous _).mul (hb.mul F.continuous)).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [norm_mul, leftPhase_norm, one_mul, norm_mul]
  calc
    _ ≤ (M * (1 + ‖ξ‖)) * ‖F ξ‖ := mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _)
    _ = _ := by simp only [Pi.add_apply, pow_one]; ring

/-- The genuine spatial differentiation commutator for the actual left
quantization, on the fixed Schwartz input and its actual directional derivative. -/
theorem firstOrderAction_direction_commutator {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a)
    (hBase : ∀ x e, Continuous (baseDirectionSymbol a e x))
    (f : SchwartzMap E ℂ) (x e : E) :
    deriv (fun t : ℝ => firstOrderAction a f (x + t • e)) 0 -
      firstOrderAction a (SchwartzMap.pderivCLM ℂ e f) x =
      firstOrderAction (baseDirectionSymbol a e) f x := by
  obtain ⟨D,_,hD⟩ := ha.order 0
  have hGrowBase (ξ : E) : ‖baseDirectionSymbol a e x ξ‖ ≤ (D * ‖e‖) * (1 + ‖ξ‖) :=
    baseDirectionSymbol_grow ha (fun y z => by simpa only [pow_zero, mul_one] using hD y z) x e ξ
  obtain ⟨M,_,hM⟩ := ha.frequency.order 0
  let df := SchwartzMap.pderivCLM ℂ e f
  have hFourier (ξ : E) : (𝓕 (df : E → ℂ)) ξ = leftPhaseRate e ξ * (𝓕 (f : E → ℂ)) ξ := by
    rw [show (𝓕 (df : E → ℂ)) ξ = _ from Burnett.Analysis.HminusWeightedDual.fourier_pderiv f e ξ]
    unfold leftPhaseRate
    push_cast
    ring
  have hIntD := integrable_phase_symbol (hBase x e) hGrowBase f x
  have hIntA := integrable_phase_symbol (ha.frequency.smooth x).continuous
    (fun ξ => by simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hM x ξ) df x
  rw [(firstOrderAction_line_hasDerivAt ha hBase f x e).deriv,
    firstOrderAction_eq_integral, firstOrderAction_eq_integral]
  apply sub_eq_iff_eq_add.mpr
  rw [← integral_add hIntD hIntA]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hFourier]
  ring

end Burnett.Analysis.FirstOrderDyadic
