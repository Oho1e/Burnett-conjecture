import Burnett.Analysis.AllScaleTransfer.ActualLowEndpointParaproductLp3
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.A05
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Filter Burnett.Fourier Burnett.A02.FrequencySplit
open Burnett.Microlocal.AngularCommutator
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight radialLowCutoff
  radialAnnularCutoff thickProductCutoff radialBallBump)
open Burnett.A03 (spatialModePhase)
open scoped ENNReal RealInnerProductSpace FourierTransform

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

theorem endpointModeSymbol_measurable (P : ℝ) (a : FourierMode) :
    Measurable (endpointModeSymbol P a) := by
  have hdir : Measurable endpointDirection := by unfold endpointDirection; fun_prop
  have hphase : Continuous (spatialModePhase P a : E → ℝ) := by unfold spatialModePhase; fun_prop
  have hexp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by fun_prop
  exact hexp.measurable.comp (hphase.measurable.comp hdir)

private def angularWindowSpectrum (P : ℝ) (a : FourierMode)
    (b f : SchwartzMap E ℂ) (s : ℝ) (ξ : E) : ℂ :=
  b (s • ξ) * endpointModeSymbol P a ξ * 𝓕 (f : E → ℂ) ξ

private theorem angularWindowSpectrum_measurable (P : ℝ) (a : FourierMode)
    (b f : SchwartzMap E ℂ) (s : ℝ) : Measurable (angularWindowSpectrum P a b f s) := by
  unfold angularWindowSpectrum
  exact ((b.continuous.comp (continuous_const_smul _)).measurable.mul
    (endpointModeSymbol_measurable P a)).mul (SchwartzMap.fourierTransformCLM ℂ f).continuous.measurable

private theorem angularWindowSpectrum_integrable (P : ℝ) (a : FourierMode)
    (b f : SchwartzMap E ℂ) (s : ℝ) : Integrable (angularWindowSpectrum P a b f s) := by
  refine (SchwartzMap.fourierTransformCLM ℂ f).integrable.bdd_mul' (c := SchwartzMap.seminorm ℝ 0 0 b)
    (((b.continuous.comp (continuous_const_smul _)).measurable.mul
      (endpointModeSymbol_measurable P a)).aestronglyMeasurable) ?_
  refine Eventually.of_forall (fun ξ => ?_)
  rw [norm_mul, endpointModeSymbol_norm, mul_one]
  exact b.norm_le_seminorm ℝ _

private theorem angularWindowLp3_eq_inverse (P : ℝ) (a : FourierMode)
    (b : SchwartzMap E ℂ) (hb : HasCompactSupport (b : E → ℂ)) (s : ℝ) (hs : 0 < s)
    (f : SchwartzMap E ℂ) (F : EndpointLp3)
    (hF : (F : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (endpointModeBoundedSymbol P a) (f.toLp 2 volume) : E → ℂ)) :
    (endpointWindowLp3 b s hs F : E → ℂ) =ᵐ[volume] 𝓕⁻ (angularWindowSpectrum P a b f s) := by
  let M := endpointModeBoundedSymbol P a
  let B := rescaleSymbol (modulatedWindowSymbol b 0) s hs
  let X := fourierMultiplier M (f.toLp 2 volume)
  have h₂ : MemLp (F : E → ℂ) 2 volume := (Lp.memLp X).ae_eq hF.symm
  have hTo : h₂.toLp (F : E → ℂ) = X := Lp.ext (h₂.coeFn_toLp.trans hF)
  have hWin := endpointWindowLp3_intersection b hb s hs (F : E → ℂ) h₂ (Lp.memLp F)
  rw [Lp.toLp_coeFn, hTo] at hWin
  let Y := symbolL2 B (fourierL2Equiv X)
  have hY : (Y : E → ℂ) =ᵐ[volume] angularWindowSpectrum P a b f s := by
    have hFourier : fourierL2Equiv X = symbolL2 M (fourierL2Equiv (f.toLp 2 volume)) :=
      fourier_fourierMultiplier M _
    unfold Y
    rw [hFourier]
    filter_upwards [symbolL2_ae B (symbolL2 M (fourierL2Equiv (f.toLp 2 volume))),
      symbolL2_ae M (fourierL2Equiv (f.toLp 2 volume)), fourierL2Equiv_schwartz_ae f] with ξ h₁ h₂' h₃
    rw [h₁,h₂',h₃]
    change rescaleSymbol (modulatedWindowSymbol b 0) s hs ξ *
      (endpointModeSymbol P a ξ * _) = _
    rw [endpointWindowSymbol_eval, angularWindowSpectrum, mul_assoc]
  have hS := (Lp.memLp Y).ae_eq hY
  have hEq : Y = hS.toLp (angularWindowSpectrum P a b f s) := Lp.ext (hY.trans hS.coeFn_toLp.symm)
  refine hWin.trans ?_
  change (fourierL2Equiv.symm Y : E → ℂ) =ᵐ[volume] _
  rw [hEq]
  exact fourierL2Equiv_symm_eq_inverse_ae_of_integrable _
    (angularWindowSpectrum_integrable P a b f s) hS

private def inversionPhase (r : ℝ) : ℂ := Complex.exp ((↑(tau * r) : ℂ) * Complex.I)

private theorem inversionPhase_norm (r : ℝ) : ‖inversionPhase r‖ = 1 := by
  simp [inversionPhase, Complex.norm_exp]

private theorem inversionPhase_add (r s : ℝ) :
    inversionPhase (r+s) = inversionPhase r * inversionPhase s := by
  unfold inversionPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- The first two inverse transforms need only integrable spectra.
private theorem inverse_spectra_product_integral (F G : E → ℂ) (mF : Measurable F) (mG : Measurable G)
    (hF : Integrable F) (hG : Integrable G) (H : SchwartzMap E ℂ) :
    (∫ x, 𝓕⁻ F x * 𝓕⁻ G x * H x) =
      ∫ p : Joint, F p.1 * G p.2 * 𝓕 (H : E → ℂ) (-(p.1+p.2)) := by
  let U (p : Joint) := F p.1 * G p.2
  let O (x : E) (p : Joint) := inversionPhase (inner ℝ p.1 x + inner ℝ p.2 x)
  let V (x : E) (p : Joint) := U p * (O x p * H x)
  have intU : Integrable U := by rw [Measure.volume_eq_prod E E]; exact hF.mul_prod hG
  have mU : Measurable U := (mF.comp measurable_fst).mul (mG.comp measurable_snd)
  have intV : Integrable (Function.uncurry V) ((volume : Measure E).prod volume) := by
    have mO : Measurable (fun z : E × Joint => O z.1 z.2) := by unfold O inversionPhase; fun_prop
    refine (H.integrable.norm.mul_prod intU.norm).mono'
      (((mU.comp measurable_snd).mul (mO.mul (H.continuous.measurable.comp measurable_fst))).aestronglyMeasurable) ?_
    filter_upwards with z
    change ‖U z.2 * (O z.1 z.2 * H z.1)‖ ≤ ‖H z.1‖ * ‖U z.2‖
    simp only [O, norm_mul, inversionPhase_norm, one_mul]
    exact le_of_eq (mul_comm _ _)
  have point (x : E) : 𝓕⁻ F x * 𝓕⁻ G x * H x = ∫ p, V x p := by
    rw [Real.fourierIntegralInv_eq', Real.fourierIntegralInv_eq']
    change ((∫ ξ, inversionPhase (inner ℝ ξ x) * F ξ) *
      (∫ η, inversionPhase (inner ℝ η x) * G η)) * H x = _
    rw [← integral_prod_mul (fun ξ => inversionPhase (inner ℝ ξ x) * F ξ)
      (fun η => inversionPhase (inner ℝ η x) * G η), ← integral_mul_const, ← Measure.volume_eq_prod E E]
    apply integral_congr_ae
    filter_upwards with p
    simp only [V,U,O,inversionPhase_add]
    ring
  have phasePair (p : Joint) : (∫ x, O x p * H x) = 𝓕 (H : E → ℂ) (-(p.1+p.2)) := by
    rw [Real.fourierIntegral_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [O,inversionPhase,inner_neg_right,inner_add_right,real_inner_comm x p.1,
      real_inner_comm x p.2,smul_eq_mul,neg_mul,mul_neg,neg_neg]
  simp_rw [point]
  rw [integral_integral_swap intV]
  apply integral_congr_ae
  filter_upwards with p
  change (∫ x, U p * (O x p * H x)) = _
  rw [integral_const_mul,phasePair]

private theorem radianForm_eq_cycles (m : Joint → ℂ) (f g w : SchwartzMap E ℂ) :
    radianTrilinearForm m f g w =
      ∫ p : Joint, m (tau • p) * (𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2) *
        𝓕 (w : E → ℂ) (-(p.1+p.2)) := by
  letI := jointVolume_haar
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod, dimE]
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint)
    (radianTrilinearWeight m f g w) tau (hR := (mul_pos (by norm_num) Real.pi_pos).le)
  rw [dimJoint] at changeFreq
  unfold radianTrilinearForm
  rw [← changeFreq]
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul, Prod.smul_fst,
    Prod.smul_snd, ← smul_add, ← smul_neg, radianFourier_scaled, mul_assoc]

/-- The three original windows, with the thick window on the negative-sum frequency. -/
def lowEndpointRadianWindows (gap : ℕ) (j : ℤ) (p : Joint) : ℂ :=
  (radialLowCutoff ((2 : ℝ)^j / (2 : ℝ)^gap) p.1 : ℂ) *
    (radialAnnularCutoff ((2 : ℝ)^j) p.2 : ℂ) *
    (thickProductCutoff ((2 : ℝ)^j) (-(p.1+p.2)) : ℂ)

theorem lowEndpointRadianWindows_eq_profiles (gap : ℕ) (j : ℤ) (p : Joint) :
    lowEndpointRadianWindows gap j p =
      endpointLowProfile (((2 : ℝ)^gap * endpointScale j) • (tau⁻¹ • p.1)) *
        endpointHighProfile (endpointScale j • (tau⁻¹ • p.2)) *
        endpointThickProfile (endpointScale j • (tau⁻¹ • (-(p.1+p.2)))) := by
  let r := (2 : ℝ)^j
  have hlow : tau * (r / (2 : ℝ)^gap)⁻¹ = (2 : ℝ)^gap * endpointScale j := by
    rw [inv_div,div_eq_mul_inv,endpointScale,zpow_neg]
    dsimp only [r]
    ring
  have hhigh : tau * r⁻¹ = endpointScale j := by
    simp only [endpointScale,r,zpow_neg,mul_comm]
  have h₁ := (endpoint_profiles_at_radian_frequency r gap p.1).1
  have h₂ := (endpoint_profiles_at_radian_frequency r gap p.2).2.1
  have h₃ := (endpoint_profiles_at_radian_frequency r gap (-(p.1+p.2))).2.2
  dsimp only at h₁ h₂ h₃
  rw [hlow] at h₁
  rw [hhigh] at h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

def angularLowEndpointModeSymbol (P : ℝ) (ab : FourierModePair) (gap : ℕ) (j : ℤ) (p : Joint) : ℂ :=
  endpointModeSymbol P ab.1 p.1 * endpointModeSymbol P ab.2 p.2 * lowEndpointRadianWindows gap j p

private theorem angularLowEndpoint_mode_term (P : ℝ) (ab : FourierModePair) (gap : ℕ) (j : ℤ)
    (f g w : SchwartzMap E ℂ) (F G : EndpointLp3)
    (hF : (F : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (endpointModeBoundedSymbol P ab.1) (f.toLp 2 volume) : E → ℂ))
    (hG : (G : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (endpointModeBoundedSymbol P ab.2) (g.toLp 2 volume) : E → ℂ)) :
    (∫ x, endpointLowWindowLp3 gap j F x * endpointHighWindowLp3 j G x *
      endpointThickWindowLp3 j (w.toLp (ENNReal.ofReal 3) volume) x) =
      radianTrilinearForm (angularLowEndpointModeSymbol P ab gap j) f g w := by
  let s := (2 : ℝ)^gap * endpointScale j
  let t := endpointScale j
  have htau : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have ht : 0 < t := mul_pos (by positivity) htau
  have hs : 0 < s := mul_pos (by positivity) ht
  have hlow : HasCompactSupport (endpointLowProfile : E → ℂ) :=
    radialBallBump.hasCompactSupport.comp_left Complex.ofReal_zero
  let U := angularWindowSpectrum P ab.1 endpointLowProfile f s
  let V := angularWindowSpectrum P ab.2 endpointHighProfile g t
  let H := windowTest endpointThickProfile w t
  have hu : (endpointLowWindowLp3 gap j F : E → ℂ) =ᵐ[volume] 𝓕⁻ U :=
    angularWindowLp3_eq_inverse P ab.1 endpointLowProfile hlow s hs f F hF
  have hv : (endpointHighWindowLp3 j G : E → ℂ) =ᵐ[volume] 𝓕⁻ V :=
    angularWindowLp3_eq_inverse P ab.2 endpointHighProfile endpointHighProfile_properties.2.1 t ht g G hG
  have hw : (endpointThickWindowLp3 j (w.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume] (H : E → ℂ) := by
    refine (endpointWindowLp3_Schwartz endpointThickProfile w t ht).trans (Eventually.of_forall fun x => ?_)
    simpa only [H,neg_zero,zero_div,smul_zero,sub_zero] using
      (windowTest_translate endpointThickProfile w t 0 ht x (0 : E)).symm
  have eq : (∫ x, endpointLowWindowLp3 gap j F x * endpointHighWindowLp3 j G x *
      endpointThickWindowLp3 j (w.toLp (ENNReal.ofReal 3) volume) x) =
      ∫ x, 𝓕⁻ U x * 𝓕⁻ V x * H x := by
    apply integral_congr_ae
    filter_upwards [hu,hv,hw] with x hx hy hz
    rw [hx,hy,hz]
  rw [eq,inverse_spectra_product_integral U V (angularWindowSpectrum_measurable ..)
    (angularWindowSpectrum_measurable ..) (angularWindowSpectrum_integrable ..)
    (angularWindowSpectrum_integrable ..) H,radianForm_eq_cycles]
  apply integral_congr_ae
  filter_upwards with p
  rw [show 𝓕 (H : E → ℂ) (-(p.1+p.2)) =
    𝓕 (w : E → ℂ) (-(p.1+p.2)) * endpointThickProfile (t • (-(p.1+p.2))) from
      windowTest_fourier endpointThickProfile w t _]
  simp only [U,V,angularWindowSpectrum,angularLowEndpointModeSymbol,lowEndpointRadianWindows_eq_profiles,
    Prod.smul_fst,Prod.smul_snd,endpointModeSymbol_pos_smul P _ tau htau,
    smul_smul,inv_mul_cancel₀ htau.ne',mul_one,← smul_add,← smul_neg]
  dsimp only [s,t]
  ring

/-- The actual finite spatial sum on the angular outputs is the corresponding
complex radian integral at each scale. -/
theorem lowEndpointParaproductLp3_mode_radian (P : ℝ) (ab : FourierModePair) (gap : ℕ)
    {n : ℕ} (j : Fin n ↪ ℤ) (f g w : SchwartzMap E ℂ) (F G : EndpointLp3)
    (hF : (F : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (endpointModeBoundedSymbol P ab.1) (f.toLp 2 volume) : E → ℂ))
    (hG : (G : E → ℂ) =ᵐ[volume]
      (fourierMultiplier (endpointModeBoundedSymbol P ab.2) (g.toLp 2 volume) : E → ℂ)) :
    lowEndpointParaproductLp3 gap j F G (w.toLp (ENNReal.ofReal 3) volume) =
      ∑ i : Fin n, radianTrilinearForm (angularLowEndpointModeSymbol P ab gap (j i)) f g w := by
  rw [(lowEndpointParaproductLp3_eq_integral gap j _ _ _).2]
  exact Finset.sum_congr rfl (fun i _ => angularLowEndpoint_mode_term P ab gap (j i) f g w F G hF hG)

end Burnett.A05
