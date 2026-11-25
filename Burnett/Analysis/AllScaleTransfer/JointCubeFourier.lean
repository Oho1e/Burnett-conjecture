-- Specialization of the A03 fixed cube to the two four-dimensional inputs.
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.A05.BoxFourier

open MeasureTheory Metric Set
open scoped FourierTransform ContDiff RealInnerProductSpace

abbrev BoxIndex := Fin 4 ⊕ Fin 4
abbrev BoxSpace := EuclideanSpace ℝ BoxIndex

/-- The fixed coordinate cube using the usual Euclidean volume. -/
def boxFourierCube (P : ℝ) : Set BoxSpace :=
  {y | ∀ j : BoxIndex, -P ≤ y j ∧ y j ≤ P}

private theorem cube_eq_preimage (P : ℝ) :
    boxFourierCube P =
      (WithLp.ofLp (p := 2)) ⁻¹' Icc (fun _ : BoxIndex => -P) (fun _ : BoxIndex => P) := by
  ext y
  change (∀ j : BoxIndex, -P ≤ y j ∧ y j ≤ P) ↔
    (∀ j : BoxIndex, -P ≤ y j) ∧ (∀ j : BoxIndex, y j ≤ P)
  exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩

theorem box_fourier_cube_volume (P : ℝ) :
    (volume : Measure BoxSpace) (boxFourierCube P) = (ENNReal.ofReal (2 * P)) ^ 8 := by
  have hBox : MeasurableSet (Icc (fun _ : BoxIndex => -P) (fun _ : BoxIndex => P)) := measurableSet_Icc
  rw [cube_eq_preimage, (PiLp.volume_preserving_ofLp (ι := BoxIndex)).measure_preimage hBox.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin]
  rfl

theorem closed_ball_subset_box_fourier_cube (S P : ℝ) (h : S ≤ P) :
    closedBall (0 : BoxSpace) S ⊆ boxFourierCube P := by
  intro y hy j
  have hn : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hv : |y j| ≤ P := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hn.trans h)
  exact abs_le.mp hv

/-- The integer lattice embedded in the identical Euclidean coordinate space. -/
def boxLatticeVector (k : BoxIndex → ℤ) : BoxSpace :=
  WithLp.toLp 2 (fun j : BoxIndex => (k j : ℝ))

def boxModeFrequency (P : ℝ) (k : BoxIndex → ℤ) : BoxSpace :=
  (2 * P)⁻¹ • boxLatticeVector k

def boxModePhase (P : ℝ) (k : BoxIndex → ℤ) (y : BoxSpace) : ℝ :=
  2 * Real.pi * inner ℝ y (boxModeFrequency P k)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The genuine Fourier coefficient with the negative phase and the exact
cube volume normalization. -/
def boxCubeFourierCoefficient (P : ℝ) (k : BoxIndex → ℤ)
    (f : BoxSpace → F) : F :=
  ((2 * P) ^ 8)⁻¹ • ∫ y in boxFourierCube P,
    Complex.exp ((↑(-boxModePhase P k y) : ℂ) * Complex.I) • f y

/-- A supported profile has the literal whole-space Fourier-integral
representation of the same coefficient. -/
theorem box_cube_fourier_coefficient_eq_fourier (P : ℝ) (k : BoxIndex → ℤ)
    (f : BoxSpace → F) (hz : ∀ y ∉ boxFourierCube P, f y = 0) :
    boxCubeFourierCoefficient P k f =
      ((2 * P) ^ 8)⁻¹ • 𝓕 f (boxModeFrequency P k) := by
  unfold boxCubeFourierCoefficient
  rw [Real.fourierIntegral_eq']
  simp only [boxModePhase, ← neg_mul]
  apply congrArg (fun z : F => ((2 * P) ^ 8)⁻¹ • z)
  let g (y : BoxSpace) := Complex.exp
    ((↑(-2 * Real.pi * inner ℝ y (boxModeFrequency P k)) : ℂ) * Complex.I) • f y
  have hg (y : BoxSpace) (hy : y ∉ boxFourierCube P) : g y = 0 := by
    simp only [g, hz y hy, smul_zero]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hg

/-- The normalization makes the coefficient no larger than a uniform bound
on the original profile in the cube. -/
theorem box_cube_fourier_coefficient_norm_le (P : ℝ) (hP : 0 < P) (k : BoxIndex → ℤ)
    (f : BoxSpace → F) (M : ℝ)
    (hM : ∀ y ∈ boxFourierCube P, ‖f y‖ ≤ M) :
    ‖boxCubeFourierCoefficient P k f‖ ≤ M := by
  have volumeFinite : (volume : Measure BoxSpace) (boxFourierCube P) < ⊤ := by
    rw [box_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have volumeReal : (volume : Measure BoxSpace).real (boxFourierCube P) = (2 * P) ^ 8 := by
    rw [Measure.real, box_fourier_cube_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  have hI : ‖∫ y in boxFourierCube P,
      Complex.exp ((↑(-boxModePhase P k y) : ℂ) * Complex.I) • f y‖ ≤ M * (2 * P) ^ 8 := by
    rw [← volumeReal]
    apply norm_setIntegral_le_of_norm_le_const_ae' volumeFinite
    exact Filter.Eventually.of_forall fun y hy => by
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hM y hy
  unfold boxCubeFourierCoefficient
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 * P) ^ 8)⁻¹ * (M * (2 * P) ^ 8) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M := by
      rw [mul_comm M, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * P) ^ 8 ≠ 0), one_mul]

end Burnett.A05.BoxFourier
