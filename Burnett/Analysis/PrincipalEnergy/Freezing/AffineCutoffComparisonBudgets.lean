import Burnett.Analysis.PrincipalEnergy.Freezing.ProfileFourierMoment
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedEnergyFields

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal

/-- Exact pointwise coordinate derivative of the same affine rescaling. -/
theorem affine_test_cutoff_coordinate (f g : SchwartzMap E ℂ) (c : E) (ℓ : ℝ)
    (same : ∀ x, g x = f (ℓ⁻¹ • (x-c))) (j : Index) (x : E) :
    energyPartial j g x = ℓ⁻¹ • energyPartial j f (ℓ⁻¹ • (x-c)) := by
  have hg : (g : E → ℂ) = fun y => f (ℓ⁻¹ • (y-c)) := funext same
  have d : HasFDerivAt (fun y : E => ℓ⁻¹ • (y-c)) (ℓ⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul ℓ⁻¹
  have p := ((f.differentiable (ℓ⁻¹ • (x-c))).hasFDerivAt).comp x d
  simp only [energyPartial, SchwartzMap.pderivCLM_apply, hg]
  change fderiv ℝ ((f : E → ℂ) ∘ (fun y => ℓ⁻¹ • (y-c))) x (EuclideanSpace.single j 1) = _
  rw [p.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul]

/-- Exact Fourier moment scaling and finite center-independent derivative
budgets at each fixed scale used by the actual cutoff commutator. -/
theorem affine_test_cutoff_uniform_budgets (f : SchwartzMap E ℂ) (θ : E → SchwartzMap E ℂ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (same : ∀ c x, θ c x = f (ℓ⁻¹ • (x-c))) :
    let P := ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0) f)
    let T := ENNReal.ofReal (ℓ⁻¹ * ∑ j : Index, (SchwartzMap.seminorm ℝ 0 0) (energyPartial j f))
    P < ⊤ ∧ T < ⊤ ∧ ∀ c : E,
      eLpNorm (θ c : E → ℂ) ⊤ volume ≤ P ∧
      (∀ j : Index, eLpNorm (energyPartial j (θ c) : E → ℂ) ⊤ volume ≤ T) ∧
      ∀ r : ℕ, patchFourierMoment r (θ c) = (ℓ ^ r)⁻¹ * patchFourierMoment r f := by
  intro P T
  refine ⟨ENNReal.ofReal_lt_top,ENNReal.ofReal_lt_top,?_⟩
  intro c
  refine ⟨?_,?_,?_⟩
  · rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    exact Eventually.of_forall fun x => (same c x).symm ▸ SchwartzMap.norm_le_seminorm ℝ f _
  · intro j
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    rw [affine_test_cutoff_coordinate f (θ c) c ℓ (same c) j x, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    exact mul_le_mul_of_nonneg_left
      ((SchwartzMap.norm_le_seminorm ℝ (energyPartial j f) _).trans
        (Finset.single_le_sum (f := fun i : Index => (SchwartzMap.seminorm ℝ 0 0) (energyPartial i f))
          (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (energyPartial i f)) (Finset.mem_univ j))) (inv_nonneg.mpr hℓ.le)
  · intro r
    rw [show (θ c : E → ℂ) = (fun x => f (ℓ⁻¹ • (x-c))) from funext (same c)]
    exact patch_fourier_moment_affine r f c ℓ hℓ

end Burnett.A03
