import Burnett.Analysis.AllScaleTransfer.JointCubeTorusLift
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A05.BoxFourier

open MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace Pointwise
attribute [local instance] Real.fact_zero_lt_one

private def unitTorusHaar : Measure (UnitAddTorus BoxIndex) :=
  Measure.pi fun _ : BoxIndex => AddCircle.haarAddCircle (T := 1)

theorem centered_unit_torus_measure_preserving :
    MeasurePreserving centeredUnitTorusMod
      ((volume : Measure (BoxIndex → ℝ)).restrict centeredUnitFourierCube) unitTorusHaar := by
  have circle : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      ((volume : Measure ℝ).restrict (Icc (-(1 / 2)) (1 / 2)))
      (AddCircle.haarAddCircle (T := 1)) := by
    have h := AddCircle.measurePreserving_mk (1 : ℝ) (-(1 / 2))
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      restrict_Ioc_eq_restrict_Icc,
      AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at h
    exact h
  unfold centeredUnitFourierCube unitTorusHaar
  change MeasurePreserving centeredUnitTorusMod
    ((Measure.pi fun _ : BoxIndex => (volume : Measure ℝ)).restrict (Icc (fun _ => -(1 / 2)) (fun _ => 1 / 2)))
    _
  rw [← pi_univ_Icc, Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ (fun _ : BoxIndex => circle)

/-- The physical Fourier cube is the image of the centered unit cube under
this scalar dilation in the same Euclidean space. -/
def boxRescaleFromUnitCube (P : ℝ) (x : BoxIndex → ℝ) : BoxSpace :=
  (2 * P) • WithLp.toLp 2 x

theorem box_rescale_mem_cube (P : ℝ) (hP : 0 < P) (x : BoxIndex → ℝ) :
    boxRescaleFromUnitCube P x ∈ boxFourierCube P ↔ x ∈ centeredUnitFourierCube := by
  have hp : 0 < 2 * P := by positivity
  change (∀ j : BoxIndex, -P ≤ (2 * P) * x j ∧ (2 * P) * x j ≤ P) ↔
    ((∀ j : BoxIndex, -(1 / 2 : ℝ) ≤ x j) ∧ (∀ j : BoxIndex, x j ≤ 1 / 2))
  have lower (j : BoxIndex) : -P ≤ (2 * P) * x j ↔ -(1 / 2 : ℝ) ≤ x j := by
    simpa only [show (2 * P) * (-(1 / 2 : ℝ)) = -P by ring] using
      (mul_le_mul_iff_right₀ hp : (2 * P) * (-(1 / 2 : ℝ)) ≤ (2 * P) * x j ↔ _)
  have upper (j : BoxIndex) : (2 * P) * x j ≤ P ↔ x j ≤ 1 / 2 := by
    simpa only [show (2 * P) * (1 / 2 : ℝ) = P by ring] using
      (mul_le_mul_iff_right₀ hp : (2 * P) * x j ≤ (2 * P) * (1 / 2 : ℝ) ↔ _)
  exact ⟨fun h => ⟨fun j => (lower j).1 (h j).1, fun j => (upper j).1 (h j).2⟩,
    fun h j => ⟨(lower j).2 (h.1 j), (upper j).2 (h.2 j)⟩⟩

private theorem box_rescale_cube_image (P : ℝ) (hP : 0 < P) :
    (2 * P) • (WithLp.ofLp (p := 2) ⁻¹' centeredUnitFourierCube) = boxFourierCube P := by
  have h2 : 2 * P ≠ 0 := by positivity
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ h2]
  change WithLp.ofLp ((2 * P)⁻¹ • y) ∈ centeredUnitFourierCube ↔ y ∈ boxFourierCube P
  rw [← box_rescale_mem_cube P hP (WithLp.ofLp ((2 * P)⁻¹ • y))]
  simp only [boxRescaleFromUnitCube, WithLp.toLp_ofLp, smul_smul, mul_inv_cancel₀ h2, one_smul]

private theorem box_mode_phase_rescale (P : ℝ) (hP : 0 < P) (k : BoxIndex → ℤ) (x : BoxIndex → ℝ) :
    boxModePhase P k (boxRescaleFromUnitCube P x) =
      2 * Real.pi * ∑ j : BoxIndex, (k j : ℝ) * x j := by
  have h2 : 2 * P ≠ 0 := by positivity
  unfold boxModePhase boxModeFrequency boxRescaleFromUnitCube
  have innerScale :
      inner ℝ ((2 * P) • WithLp.toLp 2 x) ((2 * P)⁻¹ • boxLatticeVector k) =
        inner ℝ (WithLp.toLp 2 x) (boxLatticeVector k) := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  rw [innerScale]
  congr 1

/-- The period-one torus character has exactly the phase used by the
physical Fourier cube coefficient. -/
theorem unit_torus_character_eq_box_phase (P : ℝ) (hP : 0 < P)
    (k : BoxIndex → ℤ) (x : BoxIndex → ℝ) :
    UnitAddTorus.mFourier k (centeredUnitTorusMod x) =
      Complex.exp ((boxModePhase P k (boxRescaleFromUnitCube P x) : ℂ) * Complex.I) := by
  rw [box_mode_phase_rescale P hP, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  simp_rw [centeredUnitTorusMod, fourier_coe_apply (T := 1), Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem negative_character_eq_box_phase (P : ℝ) (hP : 0 < P)
    (k : BoxIndex → ℤ) (x : BoxIndex → ℝ) :
    UnitAddTorus.mFourier (-k) (centeredUnitTorusMod x) =
      Complex.exp ((↑(-boxModePhase P k (boxRescaleFromUnitCube P x)) : ℂ) * Complex.I) := by
  rw [unit_torus_character_eq_box_phase P hP, box_mode_phase_rescale P hP,
    box_mode_phase_rescale P hP]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- The normalized coefficient from the original real-space cube equals
the corresponding actual Haar Fourier coefficient of its unit torus lift. -/
theorem unit_torus_coefficient_eq_box_cube (P : ℝ) (hP : 0 < P) (g : BoxSpace → ℂ)
    (G : C(UnitAddTorus BoxIndex, ℂ))
    (agrees : ∀ x ∈ centeredUnitFourierCube, G (centeredUnitTorusMod x) = g (boxRescaleFromUnitCube P x))
    (k : BoxIndex → ℤ) :
    UnitAddTorus.mFourierCoeff G k = boxCubeFourierCoefficient P k g := by
  let F (t : UnitAddTorus BoxIndex) := UnitAddTorus.mFourier (-k) t • G t
  have hF : Continuous F := (UnitAddTorus.mFourier (-k)).continuous.smul G.continuous
  let f (y : BoxSpace) := Complex.exp ((↑(-boxModePhase P k y) : ℂ) * Complex.I) • g y
  change (∫ t, F t ∂unitTorusHaar) = _
  rw [← centered_unit_torus_measure_preserving.map_eq,
    integral_map centered_unit_torus_measure_preserving.measurable.aemeasurable hF.aestronglyMeasurable]
  calc
    _ = ∫ x in centeredUnitFourierCube, f (boxRescaleFromUnitCube P x) := by
      apply setIntegral_congr_fun (by exact measurableSet_Icc)
      intro x hx
      simp only [F, f, negative_character_eq_box_phase P hP, agrees x hx]
    _ = ∫ y in WithLp.ofLp (p := 2) ⁻¹' centeredUnitFourierCube, f ((2 * P) • y) := by
      have he := (PiLp.volume_preserving_ofLp (ι := BoxIndex)).setIntegral_preimage_emb
        (PiLp.homeomorph 2 (fun _ : BoxIndex => ℝ)).toMeasurableEquiv.measurableEmbedding
        (f ∘ boxRescaleFromUnitCube P) centeredUnitFourierCube
      simpa only [Function.comp_apply, boxRescaleFromUnitCube, WithLp.toLp_ofLp] using he.symm
    _ = _ := by
      rw [Measure.setIntegral_comp_smul_of_pos volume f _ (by positivity : 0 < 2 * P),
        show Module.finrank ℝ BoxSpace = 8 by simp [BoxSpace, BoxIndex, finrank_euclideanSpace], box_rescale_cube_image P hP]
      rfl

end Burnett.A05.BoxFourier
