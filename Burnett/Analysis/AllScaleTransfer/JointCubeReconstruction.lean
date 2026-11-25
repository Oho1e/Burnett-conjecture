import Burnett.Analysis.AllScaleTransfer.JointCubeTorusCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A05.BoxFourier

open Metric Set
open scoped ContDiff RealInnerProductSpace

private theorem support_profile_zero_on_unit_cube_face (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : BoxSpace → ℂ) (support : tsupport g ⊆ closedBall (0 : BoxSpace) S)
    (x : BoxIndex → ℝ) (face : ∃ j, x j = -(1 / 2) ∨ x j = 1 / 2) :
    g (boxRescaleFromUnitCube P x) = 0 := by
  obtain ⟨j, hj⟩ := face
  let y := boxRescaleFromUnitCube P x
  have coord : |y j| = P := by
    change |(2 * P) * x j| = P
    rcases hj with hj | hj
    · rw [hj, show 2 * P * -(1 / 2 : ℝ) = -P by ring, abs_neg, abs_of_pos hP]
    · rw [hj, show 2 * P * (1 / 2 : ℝ) = P by ring, abs_of_pos hP]
  by_contra hn
  have hball := support (subset_closure (Function.mem_support.mpr hn))
  have hLeft : P ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs, coord] using PiLp.norm_apply_le y j
  have hRight : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hball
  exact (not_le_of_gt hSP) (hLeft.trans hRight)

/-- Summable actual cube coefficients reconstruct the compactly supported
profile pointwise on the full closed cube. -/
theorem hasSum_box_cube_fourier_series (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : BoxSpace → ℂ) (hg : Continuous g)
    (support : tsupport g ⊆ closedBall (0 : BoxSpace) S)
    (summable : Summable (fun k => boxCubeFourierCoefficient P k g)) :
    ∀ y ∈ boxFourierCube P,
      HasSum (fun k : BoxIndex → ℤ => boxCubeFourierCoefficient P k g *
        Complex.exp ((boxModePhase P k y : ℂ) * Complex.I)) (g y) := by
  have hRescale : Continuous (boxRescaleFromUnitCube P) :=
    (PiLp.continuous_toLp 2 (fun _ : BoxIndex => ℝ)).const_smul _
  obtain ⟨G, agrees⟩ := exists_centered_unit_torus_lift (g ∘ boxRescaleFromUnitCube P)
    (hg.comp hRescale) (fun x _ => support_profile_zero_on_unit_cube_face P S hP hSP g support x)
  have exactCoeff (k : BoxIndex → ℤ) :
      UnitAddTorus.mFourierCoeff G k = boxCubeFourierCoefficient P k g :=
    unit_torus_coefficient_eq_box_cube P hP g G agrees k
  have hs : Summable (UnitAddTorus.mFourierCoeff G) :=
    summable.congr (fun k => (exactCoeff k).symm)
  intro y hy
  let x := WithLp.ofLp ((2 * P)⁻¹ • y)
  have h2 : 2 * P ≠ 0 := by positivity
  have exactPoint : boxRescaleFromUnitCube P x = y := by
    simp only [x, boxRescaleFromUnitCube, WithLp.toLp_ofLp, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hx := (box_rescale_mem_cube P hP x).mp (by rwa [exactPoint] :
    boxRescaleFromUnitCube P x ∈ boxFourierCube P)
  have sum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (centeredUnitTorusMod x)
  rw [agrees x hx, Function.comp_apply, exactPoint] at sum
  apply sum.congr_fun
  intro k
  rw [exactCoeff k, unit_torus_character_eq_box_phase P hP, exactPoint, smul_eq_mul]

end Burnett.A05.BoxFourier
