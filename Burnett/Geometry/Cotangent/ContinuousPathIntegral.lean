import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev TimePath (ρ : ℝ) (Y : Type*) [TopologicalSpace Y] :=
  C(Icc (-ρ) ρ, Y)

private noncomputable def intervalClamp {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : Icc (-ρ) ρ :=
  projIcc (-ρ) ρ (by linarith) t

private theorem continuous_intervalClamp {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Continuous (intervalClamp hρ) := continuous_projIcc (h := by linarith)

private noncomputable def coefficientAction {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) (u : TimePath ρ E) (t : ℝ) : E :=
  A (intervalClamp hρ t) (u (intervalClamp hρ t))

private theorem continuous_coefficientAction {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) (u : TimePath ρ E) :
    Continuous (coefficientAction hρ A u) := by
  exact (A.continuous.comp (continuous_intervalClamp hρ)).clm_apply
    (u.continuous.comp (continuous_intervalClamp hρ))

private noncomputable def volterraLinear {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) : TimePath ρ E →ₗ[ℝ] TimePath ρ E where
  toFun u :=
    ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A u s,
      (intervalIntegral.continuous_primitive (fun a b =>
        (continuous_coefficientAction hρ A u).intervalIntegrable a b) 0).comp
          continuous_subtype_val⟩
  map_add' u v := by
    ext t
    change (∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A (u + v) s) =
      (∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A u s) +
        (∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A v s)
    rw [← intervalIntegral.integral_add
      ((continuous_coefficientAction hρ A u).intervalIntegrable 0 t)
      ((continuous_coefficientAction hρ A v).intervalIntegrable 0 t)]
    simp only [coefficientAction, ContinuousMap.add_apply, map_add]
  map_smul' k u := by
    ext t
    change (∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A (k • u) s) =
      k • (∫ s in (0 : ℝ)..(t : ℝ), coefficientAction hρ A u s)
    rw [← intervalIntegral.integral_smul]
    simp only [coefficientAction, ContinuousMap.smul_apply, map_smul]

private theorem norm_volterraLinear_apply_le {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) (u : TimePath ρ E) :
    ‖volterraLinear hρ A u‖ ≤ (ρ * ‖A‖) * ‖u‖ := by
  apply (ContinuousMap.norm_le (volterraLinear hρ A u) (by positivity)).mpr
  intro t
  have ht' : |(t : ℝ) - 0| ≤ ρ := by
    rw [sub_zero, abs_le]
    exact t.property
  have hb (s : ℝ) : ‖coefficientAction hρ A u s‖ ≤ ‖A‖ * ‖u‖ :=
    ((A (intervalClamp hρ s)).le_opNorm (u (intervalClamp hρ s))).trans
      (mul_le_mul (A.norm_coe_le_norm _) (u.norm_coe_le_norm _)
        (norm_nonneg (u (intervalClamp hρ s))) (norm_nonneg A))
  calc
    ‖volterraLinear hρ A u t‖
        ≤ (‖A‖ * ‖u‖) * |(t : ℝ) - 0| := by
      exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hb s)
    _ ≤ (‖A‖ * ‖u‖) * ρ := mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = (ρ * ‖A‖) * ‖u‖ := by ring

/-- The continuous linear Volterra operator of a continuous coefficient path,
based at the common initial time zero. -/
noncomputable def timeVolterra {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) : TimePath ρ E →L[ℝ] TimePath ρ E :=
  (volterraLinear hρ A).mkContinuous (ρ * ‖A‖) (norm_volterraLinear_apply_le hρ A)

theorem timeVolterra_apply {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : TimePath ρ (E →L[ℝ] E)) (u : TimePath ρ E) (t : Icc (-ρ) ρ) :
    timeVolterra hρ A u t =
      ∫ s in (0 : ℝ)..(t : ℝ), A (projIcc (-ρ) ρ (by linarith) s)
        (u (projIcc (-ρ) ρ (by linarith) s)) :=
  rfl

noncomputable def pathPrimitive {ρ : ℝ} (hρ : 0 ≤ ρ) : TimePath ρ E →L[ℝ] TimePath ρ E :=
  timeVolterra hρ (ContinuousMap.const _ (ContinuousLinearMap.id ℝ E))

theorem pathPrimitive_apply {ρ : ℝ} (hρ : 0 ≤ ρ) (u : TimePath ρ E) (t : Icc (-ρ) ρ) :
    pathPrimitive hρ u t = ∫ s in (0 : ℝ)..(t : ℝ), u (projIcc (-ρ) ρ (by linarith) s) := by
  rw [pathPrimitive, timeVolterra_apply]
  simp only [ContinuousMap.const_apply, ContinuousLinearMap.id_apply]

end Burnett.Geometry.CotangentHamiltonInitialFamily
