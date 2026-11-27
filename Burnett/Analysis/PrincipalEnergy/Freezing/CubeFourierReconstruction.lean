import Burnett.Analysis.PrincipalEnergy.Freezing.FixedCubeTorusCoefficients
import Burnett.Analysis.PrincipalEnergy.Freezing.RealCubeFourierModes

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff RealInnerProductSpace

private theorem support_profile_zero_on_unit_cube_face (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : CoordinateSpace → ℂ) (support : tsupport g ⊆ closedBall (0 : CoordinateSpace) S)
    (x : Index → ℝ) (face : ∃ j, x j = -(1 / 2) ∨ x j = 1 / 2) :
    g (spatialRescaleFromUnitCube P x) = 0 := by
  obtain ⟨j, hj⟩ := face
  let y := spatialRescaleFromUnitCube P x
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
theorem hasSum_spatial_cube_fourier_series (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : CoordinateSpace → ℂ) (hg : Continuous g)
    (support : tsupport g ⊆ closedBall (0 : CoordinateSpace) S)
    (summable : Summable (fun k => spatialCubeFourierCoefficient P k g)) :
    ∀ y ∈ spatialFourierCube P,
      HasSum (fun k : Index → ℤ => spatialCubeFourierCoefficient P k g *
        Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I)) (g y) := by
  have hRescale : Continuous (spatialRescaleFromUnitCube P) :=
    (PiLp.continuous_toLp 2 (fun _ : Index => ℝ)).const_smul _
  obtain ⟨G, agrees⟩ := exists_centered_unit_torus_lift (g ∘ spatialRescaleFromUnitCube P)
    (hg.comp hRescale) (fun x _ => support_profile_zero_on_unit_cube_face P S hP hSP g support x)
  have exactCoeff (k : Index → ℤ) :
      UnitAddTorus.mFourierCoeff G k = spatialCubeFourierCoefficient P k g :=
    unit_torus_coefficient_eq_spatial_cube P hP g G agrees k
  have hs : Summable (UnitAddTorus.mFourierCoeff G) :=
    summable.congr (fun k => (exactCoeff k).symm)
  intro y hy
  let x := WithLp.ofLp ((2 * P)⁻¹ • y)
  have h2 : 2 * P ≠ 0 := by positivity
  have exactPoint : spatialRescaleFromUnitCube P x = y := by
    simp only [x, spatialRescaleFromUnitCube, WithLp.toLp_ofLp, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hx := (spatial_rescale_mem_cube P hP x).mp (by rwa [exactPoint] :
    spatialRescaleFromUnitCube P x ∈ spatialFourierCube P)
  have sum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (centeredUnitTorusMod x)
  rw [agrees x hx, Function.comp_apply, exactPoint] at sum
  apply sum.congr_fun
  intro k
  rw [exactCoeff k, unit_torus_character_eq_spatial_phase P hP, exactPoint, smul_eq_mul]

/-- The real sine and cosine terms on the whole integer lattice are the
real parts of the actual complex terms. -/
theorem hasSum_spatial_cube_real_series (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : CoordinateSpace → ℝ) (hg : Continuous g)
    (support : tsupport g ⊆ closedBall (0 : CoordinateSpace) S)
    (summable : Summable (fun k => spatialRealProfileCoefficient P k g)) :
    ∀ y ∈ spatialFourierCube P,
      HasSum (fun k : Index → ℤ =>
        (spatialRealProfileCoefficient P k g).re * Real.cos (spatialModePhase P k y) -
          (spatialRealProfileCoefficient P k g).im * Real.sin (spatialModePhase P k y)) (g y) := by
  have hSupport : tsupport (fun y => (g y : ℂ)) ⊆ closedBall (0 : CoordinateSpace) S := by
    have eq : Function.support (fun y => (g y : ℂ)) = Function.support g := by
      ext y
      simp only [Function.mem_support]
      exact not_congr Complex.ofReal_eq_zero
    change closure (Function.support (fun y => (g y : ℂ))) ⊆ _
    rw [eq]
    exact support
  intro y hy
  have realSum := Complex.reCLM.hasSum
    (hasSum_spatial_cube_fourier_series P S hP hSP (fun z => (g z : ℂ))
      (Complex.continuous_ofReal.comp hg) hSupport summable y hy)
  have target : Complex.reCLM (g y : ℂ) = g y := Complex.ofReal_re _
  rw [target] at realSum
  apply realSum.congr_fun
  intro k
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, spatialRealProfileCoefficient]

/-- Adding a support cutoff equal to one on the profile's support gives the
real separated Fourier expansion at every point of the original space. -/
theorem hasSum_cutoff_spatial_cube_real_series (P S : ℝ) (hP : 0 < P) (hSP : S < P)
    (g : CoordinateSpace → ℝ) (hg : Continuous g)
    (support : tsupport g ⊆ closedBall (0 : CoordinateSpace) S)
    (summable : Summable (fun k => spatialRealProfileCoefficient P k g))
    (ρ : CoordinateSpace → ℝ) (ρsupport : Function.support ρ ⊆ spatialFourierCube P)
    (ρone : ∀ y ∈ tsupport g, ρ y = 1) (y : CoordinateSpace) :
    HasSum (fun k : Index → ℤ =>
      (ρ y * Real.cos (spatialModePhase P k y)) * (spatialRealProfileCoefficient P k g).re +
        (ρ y * Real.sin (spatialModePhase P k y)) * (-(spatialRealProfileCoefficient P k g).im)) (g y) := by
  by_cases hy : y ∈ spatialFourierCube P
  · have sum := (hasSum_spatial_cube_real_series P S hP hSP g hg support summable y hy).mul_left (ρ y)
    have eq : ρ y * g y = g y := by
      by_cases hz : g y = 0
      · rw [hz, mul_zero]
      · rw [ρone y (subset_closure (Function.mem_support.mpr hz)), one_mul]
    rw [eq] at sum
    apply sum.congr_fun
    intro k
    ring
  · have hρ : ρ y = 0 := by
      by_contra h
      exact hy (ρsupport (Function.mem_support.mpr h))
    have hgZero : g y = 0 := by
      by_contra h
      exact hy (closed_ball_subset_spatial_fourier_cube S P hSP.le
        (support (subset_closure (Function.mem_support.mpr h))))
    simp only [hρ, hgZero, zero_mul, add_zero]
    exact hasSum_zero

end Burnett.A03
