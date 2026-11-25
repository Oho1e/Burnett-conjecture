import Burnett.Analysis.AllScaleTransfer.EndpointAngularModeJets
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05

open MeasureTheory Filter Burnett.Fourier Burnett.A02.FrequencySplit
open Burnett.Microlocal.AngularCommutator
open Burnett.A03 (spatialLatticeWeight spatialModePhase)
open scoped ContDiff FourierTransform ENNReal RealInnerProductSpace

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

abbrev EndpointLp3 := Lp ℂ (ENNReal.ofReal 3) (volume : Measure E)

def endpointModeBoundedSymbol (P : ℝ) (a : FourierMode) : BoundedSymbol E where
  toFun := endpointModeSymbol P a
  measurable := by
    have hdir : Measurable endpointDirection := by unfold endpointDirection; fun_prop
    have hphase : Continuous (spatialModePhase P a : E → ℝ) := by
      unfold spatialModePhase
      fun_prop
    have hExp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by fun_prop
    exact (hExp.measurable.comp (hphase.measurable.comp hdir)).aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun ξ => (endpointModeSymbol_norm P a ξ).le

private theorem endpointModeSymbol_eq_trig (P : ℝ) (a : FourierMode) (ξ : E) :
    endpointModeSymbol P a ξ =
      (Real.cos (endpointModePhase P a ξ) : ℂ) + Complex.I * (Real.sin (endpointModePhase P a ξ) : ℂ) := by
  rw [endpointModeSymbol, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- The actual angular mode in the manuscript's radian inverse convention. -/
def endpointModeRadianAction (P : ℝ) (a : FourierMode) (f : SchwartzMap E ℂ) (x : E) : ℂ :=
  (tau ^ 4)⁻¹ • ∫ ξ, Complex.exp ((inner ℝ ξ x : ℂ) * Complex.I) *
    (endpointModeSymbol P a ξ * radianFourier f ξ)

private theorem endpointModeRadianAction_eq_inverse (P : ℝ) (a : FourierMode)
    (f : SchwartzMap E ℂ) (x : E) :
    endpointModeRadianAction P a f x =
      𝓕⁻ (fun ξ => endpointModeSymbol P a ξ * 𝓕 (f : E → ℂ) ξ) x := by
  let F := fun ξ : E => Complex.exp ((inner ℝ ξ x : ℂ) * Complex.I) *
    (endpointModeSymbol P a ξ * radianFourier f ξ)
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure E) F tau (hR := hτ.le)
  unfold endpointModeRadianAction
  rw [dimE] at changeFreq
  rw [← changeFreq, Real.fourierIntegralInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [F, real_inner_smul_left, radianFourier_scaled, smul_eq_mul,
    endpointModeSymbol_pos_smul P a tau hτ ξ, tau]

theorem endpointMode_fourierMultiplier_Schwartz (P : ℝ) (a : FourierMode) (f : SchwartzMap E ℂ) :
    (fourierMultiplier (endpointModeBoundedSymbol P a) (f.toLp 2 volume) : E → ℂ)
      =ᵐ[volume] endpointModeRadianAction P a f := by
  let M := endpointModeBoundedSymbol P a
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := fun ξ => M ξ * F ξ
  have h₁ : Integrable G := F.integrable.bdd_mul M.measurable ⟨M.bound,M.norm_le⟩
  have he : (symbolL2 M (fourierL2Equiv (f.toLp 2 volume)) : E → ℂ) =ᵐ[volume] G := by
    filter_upwards [symbolL2_ae M (fourierL2Equiv (f.toLp 2 volume)),fourierL2Equiv_schwartz_ae f] with ξ h h'
    rw [h,h']
    rfl
  have h₂ := (Lp.memLp _).ae_eq he
  have eq : symbolL2 M (fourierL2Equiv (f.toLp 2 volume)) = h₂.toLp G :=
    Lp.ext (he.trans h₂.coeFn_toLp.symm)
  change (fourierMultiplier M (f.toLp 2 volume) : E → ℂ) =ᵐ[volume] _
  rw [fourierMultiplier_apply,eq]
  refine (fourierL2Equiv_symm_eq_inverse_ae_of_integrable G h₁ h₂).trans
    (Eventually.of_forall fun x => ?_)
  rw [endpointModeRadianAction_eq_inverse]
  rfl

private theorem endpointMode_fourierMultiplier_split (P : ℝ) (a : FourierMode)
    (Mc Ms : BoundedSymbol E)
    (hc : ∀ ξ, Mc ξ = (Real.cos (endpointModePhase P a ξ) : ℂ))
    (hs : ∀ ξ, Ms ξ = (Real.sin (endpointModePhase P a ξ) : ℂ)) (f : ComplexL2 E) :
    fourierMultiplier (endpointModeBoundedSymbol P a) f =
      fourierMultiplier Mc f + Complex.I • fourierMultiplier Ms f := by
  apply fourierL2Equiv.injective
  rw [map_add, map_smul, fourier_fourierMultiplier, fourier_fourierMultiplier, fourier_fourierMultiplier]
  let F := fourierL2Equiv f
  let M := endpointModeBoundedSymbol P a
  apply Lp.ext
  filter_upwards [symbolL2_ae M F, symbolL2_ae Mc F, symbolL2_ae Ms F,
    Lp.coeFn_add (symbolL2 Mc F) (Complex.I • symbolL2 Ms F),
    Lp.coeFn_smul Complex.I (symbolL2 Ms F)] with ξ hM hMc hMs hadd hsmul
  change symbolL2 M F ξ = (symbolL2 Mc F + Complex.I • symbolL2 Ms F) ξ
  rw [hM, hadd, Pi.add_apply, hMc, hsmul, Pi.smul_apply, hMs, hc, hs]
  change endpointModeSymbol P a ξ * F ξ =
    (Real.cos (endpointModePhase P a ξ) : ℂ) * F ξ +
      Complex.I * ((Real.sin (endpointModePhase P a ξ) : ℂ) * F ξ)
  rw [endpointModeSymbol_eq_trig]
  ring

/-- The actual complex angular exponential has a full L³ realization with the
paper's sixth-power mode loss, and agrees with the same L² and radian actions. -/
theorem exists_endpointMode_L3_bound (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : FourierMode,
      ∃ R : EndpointLp3 →L[ℂ] EndpointLp3,
        (∀ f, ‖R f‖ ≤ C * spatialLatticeWeight a ^ 6 * ‖f‖) ∧
        (∀ (f : E → ℂ) (hf : MemLp f 2 volume) (h3 : MemLp f (ENNReal.ofReal 3) volume),
          (R (h3.toLp f) : E → ℂ) =ᵐ[volume]
            (fourierMultiplier (endpointModeBoundedSymbol P a) (hf.toLp f) : E → ℂ)) ∧
        ∀ f : SchwartzMap E ℂ,
          (R (f.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume] endpointModeRadianAction P a f := by
  obtain ⟨C,hC,hMikhlin⟩ := homogeneous_multiplier_all_Lp_sphere_bound 3 (by norm_num)
  obtain ⟨D,hD,jets⟩ := exists_endpoint_trig_sphere_jets P
  refine ⟨2*C*D,by positivity,?_⟩
  intro a
  let mc := Real.cos ∘ endpointModePhase P a
  let ms := Real.sin ∘ endpointModePhase P a
  let B := D * spatialLatticeWeight a ^ 6
  have hB : 0 ≤ B := by unfold B; positivity
  have hPhase := endpointModePhase_contDiffOn P a
  have homog (T : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (ξ : E) :
      (T ∘ endpointModePhase P a) (t • ξ) = (T ∘ endpointModePhase P a) ξ :=
    congrArg T (endpointModePhase_pos_smul P a t ht ξ)
  obtain ⟨Mc,Rc,hMc,bc,ac,_⟩ := hMikhlin mc (Real.contDiff_cos.comp_contDiffOn hPhase)
    (homog Real.cos) B hB (fun j hj ξ hξ => (jets a j hj ξ hξ).1)
  obtain ⟨Ms,Rs,hMs,bs,as_,_⟩ := hMikhlin ms (Real.contDiff_sin.comp_contDiffOn hPhase)
    (homog Real.sin) B hB (fun j hj ξ hξ => (jets a j hj ξ hξ).2)
  let R : EndpointLp3 →L[ℂ] EndpointLp3 := Rc + Complex.I • Rs
  have hnorm (f : EndpointLp3) : ‖R f‖ ≤ 2*C*D * spatialLatticeWeight a ^ 6 * ‖f‖ := by
    change ‖Rc f + Complex.I • Rs f‖ ≤ _
    calc
      _ ≤ ‖Rc f‖ + ‖Complex.I • Rs f‖ := norm_add_le _ _
      _ ≤ C * B * ‖f‖ + C * B * ‖f‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
        exact add_le_add (bc f) (bs f)
      _ = _ := by unfold B; ring
  have same (f : E → ℂ) (hf : MemLp f 2 volume) (h3 : MemLp f (ENNReal.ofReal 3) volume) :
      (R (h3.toLp f) : E → ℂ) =ᵐ[volume]
        (fourierMultiplier (endpointModeBoundedSymbol P a) (hf.toLp f) : E → ℂ) := by
    rw [endpointMode_fourierMultiplier_split P a Mc Ms (fun ξ => hMc ξ) (fun ξ => hMs ξ)]
    change ((Rc (h3.toLp f) + Complex.I • Rs (h3.toLp f) : EndpointLp3) : E → ℂ) =ᵐ[volume] _
    let Fc := fourierMultiplier Mc (hf.toLp f)
    let Fs := fourierMultiplier Ms (hf.toLp f)
    filter_upwards [ac f hf h3, as_ f hf h3, Lp.coeFn_add (Rc (h3.toLp f)) (Complex.I • Rs (h3.toLp f)),
      Lp.coeFn_smul Complex.I (Rs (h3.toLp f)), Lp.coeFn_add Fc (Complex.I • Fs),
      Lp.coeFn_smul Complex.I Fs] with x xc xs xa xm ya ym
    change (Rc (h3.toLp f) + Complex.I • Rs (h3.toLp f)) x = (Fc + Complex.I • Fs) x
    rw [xa, ya, Pi.add_apply, Pi.add_apply, xm, ym, Pi.smul_apply, Pi.smul_apply, xc, xs]
  refine ⟨R,hnorm,same,?_⟩
  intro f
  exact (same f (f.memLp 2 volume) (f.memLp (ENNReal.ofReal 3) volume)).trans
    (endpointMode_fourierMultiplier_Schwartz P a f)

end Burnett.A05
