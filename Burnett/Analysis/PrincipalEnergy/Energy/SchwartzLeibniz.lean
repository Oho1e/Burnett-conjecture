import Burnett.Analysis.PrincipalEnergy.Energy.LeibnizEnergyBound
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open MeasureTheory Filter
open scoped InnerProductSpace SchwartzMap ENNReal ContDiff

abbrev Space := EuclideanSpace ℝ (Fin 4)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

def schwartzMultiplication (r : 𝓢(Space, F →L[ℂ] F)) : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F) :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ F) r.hasTemperateGrowth).toLinearMap

@[simp] theorem schwartzMultiplication_apply
    (r : 𝓢(Space, F →L[ℂ] F)) (f : 𝓢(Space, F)) (x : Space) :
    schwartzMultiplication r f x = r x (f x) := rfl

theorem schwartz_directional_leibniz (v : Space) (r : 𝓢(Space, F →L[ℂ] F)) (f : 𝓢(Space, F)) :
    SchwartzMap.pderivCLM ℂ v (schwartzMultiplication r f) =
      schwartzMultiplication r (SchwartzMap.pderivCLM ℂ v f) +
        schwartzMultiplication (SchwartzMap.pderivCLM ℂ v r) f := by
  ext x
  simp only [SchwartzMap.pderivCLM_apply, SchwartzMap.add_apply, schwartzMultiplication_apply]
  let L : (F →L[ℂ] F) →L[ℝ] (F →L[ℝ] F) := ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ
  have hr := L.hasFDerivAt.comp x (r.differentiable x).hasFDerivAt
  have hp := hr.clm_apply (f.differentiable x).hasFDerivAt
  change HasFDerivAt (↑(schwartzMultiplication r f) : Space → F) _ x at hp
  exact congrArg (fun T : Space →L[ℝ] F => T v) hp.fderiv

def schwartzToL2 : 𝓢(Space, F) →ₗ[ℂ] Lp F 2 (volume : Measure Space) :=
  (SchwartzMap.toLpCLM ℂ F 2 volume).toLinearMap

abbrev SchwartzTest (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] := ↥(LinearMap.range (schwartzToL2 (F := F)))

def schwartzTestEquiv : 𝓢(Space, F) ≃ₗ[ℂ] SchwartzTest F :=
  LinearEquiv.ofInjective (schwartzToL2 (F := F)) (SchwartzMap.injective_toLp 2 volume)

def transportSchwartzOp (T : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) : Op (SchwartzTest F) :=
  schwartzTestEquiv.toLinearMap.comp (T.comp schwartzTestEquiv.symm.toLinearMap)

@[simp] theorem transportSchwartzOp_on_equiv
    (T : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) (f : 𝓢(Space, F)) :
    transportSchwartzOp T (schwartzTestEquiv f) = schwartzTestEquiv (T f) := by
  simp [transportSchwartzOp]

@[simp] theorem schwartzTestEquiv_inner (f g : 𝓢(Space, F)) :
    ⟪schwartzTestEquiv f, schwartzTestEquiv g⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ := by
  change ⟪f.toLp 2 volume, g.toLp 2 volume⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  rw [hx, hy]

def schwartzDerivative (v : Space) : Op (SchwartzTest F) :=
  transportSchwartzOp (SchwartzMap.pderivCLM ℂ v).toLinearMap

def schwartzCoefficient (r : 𝓢(Space, F →L[ℂ] F)) : Op (SchwartzTest F) :=
  transportSchwartzOp (schwartzMultiplication r)

theorem schwartz_coefficient_leibniz (v : Space) (r : 𝓢(Space, F →L[ℂ] F)) :
    schwartzDerivative v * schwartzCoefficient r =
      schwartzCoefficient r * schwartzDerivative v + schwartzCoefficient (SchwartzMap.pderivCLM ℂ v r) := by
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  simpa only [schwartzDerivative, schwartzCoefficient, Module.End.mul_apply, LinearMap.add_apply,
    transportSchwartzOp_on_equiv, ContinuousLinearMap.coe_coe, map_add] using
      congrArg schwartzTestEquiv (schwartz_directional_leibniz v r f)

theorem schwartz_coefficient_norm_bound (r : 𝓢(Space, F →L[ℂ] F)) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ x, ‖r x‖ ≤ A) (u : SchwartzTest F) : ‖schwartzCoefficient r u‖ ≤ A * ‖u‖ := by
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  rw [schwartzCoefficient, transportSchwartzOp_on_equiv]
  change ‖(schwartzMultiplication r f).toLp 2 volume‖ ≤ A * ‖f.toLp 2 volume‖
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top]
  let a : NNReal := ⟨A, hA⟩
  have h' : ∀ᵐ x ∂(volume : Measure Space), ‖schwartzMultiplication r f x‖₊ ≤ a * ‖f x‖₊ := by
    filter_upwards with x
    have hx := ((r x).le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right (h x) (norm_nonneg _))
    exact_mod_cast (show ‖schwartzMultiplication r f x‖ ≤ (a : ℝ) * ‖f x‖ from hx)
  have hn : (a : ℝ≥0∞) = ENNReal.ofReal A := ENNReal.ofReal_coe_nnreal.symm
  simpa only [ENNReal.smul_def, smul_eq_mul, hn] using eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h' 2

theorem schwartz_coefficient_adjoint
    (r s : 𝓢(Space, F →L[ℂ] F))
    (h : ∀ x f g, ⟪r x f, g⟫_ℂ = ⟪f, s x g⟫_ℂ) (u v : SchwartzTest F) :
    ⟪schwartzCoefficient r u, v⟫_ℂ = ⟪u, schwartzCoefficient s v⟫_ℂ := by
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  obtain ⟨g, rfl⟩ := schwartzTestEquiv.surjective v
  simp only [schwartzCoefficient, transportSchwartzOp_on_equiv, schwartzTestEquiv_inner,
    schwartzMultiplication_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => h x (f x) (g x))

private def realBilinearInner : F →L[ℝ] F →L[ℝ] ℂ :=
  (LinearMap.mk₂ ℝ (inner ℂ) (fun x y z => inner_add_left x y z)
    (fun a x y => inner_smul_left_eq_smul x y a) (fun x y z => inner_add_right x y z)
    (fun a x y => inner_smul_right_eq_smul x y a)).mkContinuous₂ 1
    (fun x y => by simpa only [one_mul] using norm_inner_le_norm (𝕜 := ℂ) x y)

theorem schwartz_derivative_isSkew (v : Space) : IsSkew (schwartzDerivative (F := F) v) := by
  intro u w
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  obtain ⟨g, rfl⟩ := schwartzTestEquiv.surjective w
  simp only [schwartzDerivative, transportSchwartzOp_on_equiv, ContinuousLinearMap.coe_coe,
    schwartzTestEquiv_inner, SchwartzMap.pderivCLM_apply]
  let P := realBilinearInner (F := F)
  have hf := (SchwartzMap.bilinLeftCLM P g.hasTemperateGrowth (SchwartzMap.pderivCLM ℝ v f)).integrable
    (μ := volume)
  have hg := (SchwartzMap.bilinLeftCLM P (SchwartzMap.pderivCLM ℝ v g).hasTemperateGrowth f).integrable
    (μ := volume)
  have hfg := (SchwartzMap.bilinLeftCLM P g.hasTemperateGrowth f).integrable (μ := volume)
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume) (B := P) (v := v)
    hf hg hfg f.differentiable g.differentiable
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm, show (∫ x, ⟪f x, fderiv ℝ g x v⟫_ℂ) = -∫ x, ⟪fderiv ℝ f x v, g x⟫_ℂ from h, neg_add_cancel]

end Burnett.Analysis.SymmetricEnergy
