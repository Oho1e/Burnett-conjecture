import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped FourierTransform ContDiff RealInnerProductSpace

/-- The fixed coordinate cube using the usual Euclidean volume. -/
def spatialFourierCube (P : ℝ) : Set CoordinateSpace :=
  {y | ∀ j : Index, -P ≤ y j ∧ y j ≤ P}

private theorem cube_eq_preimage (P : ℝ) :
    spatialFourierCube P =
      (WithLp.ofLp (p := 2)) ⁻¹' Icc (fun _ : Index => -P) (fun _ : Index => P) := by
  ext y
  change (∀ j : Index, -P ≤ y j ∧ y j ≤ P) ↔
    (∀ j : Index, -P ≤ y j) ∧ (∀ j : Index, y j ≤ P)
  exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩

theorem spatial_fourier_cube_volume (P : ℝ) :
    (volume : Measure CoordinateSpace) (spatialFourierCube P) = (ENNReal.ofReal (2 * P)) ^ 4 := by
  have hBox : MeasurableSet (Icc (fun _ : Index => -P) (fun _ : Index => P)) := measurableSet_Icc
  rw [cube_eq_preimage, (PiLp.volume_preserving_ofLp (ι := Index)).measure_preimage hBox.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]
  rfl

theorem closed_ball_subset_spatial_fourier_cube (S P : ℝ) (h : S ≤ P) :
    closedBall (0 : CoordinateSpace) S ⊆ spatialFourierCube P := by
  intro y hy j
  have hn : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hv : |y j| ≤ P := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hn.trans h)
  exact abs_le.mp hv

/-- The integer lattice embedded in the identical Euclidean coordinate space. -/
def spatialLatticeVector (k : Index → ℤ) : CoordinateSpace :=
  WithLp.toLp 2 (fun j : Index => (k j : ℝ))

def spatialModeFrequency (P : ℝ) (k : Index → ℤ) : CoordinateSpace :=
  (2 * P)⁻¹ • spatialLatticeVector k

def spatialModePhase (P : ℝ) (k : Index → ℤ) (y : CoordinateSpace) : ℝ :=
  2 * Real.pi * inner ℝ y (spatialModeFrequency P k)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The genuine Fourier coefficient with the negative phase and the exact
cube volume normalization. -/
def spatialCubeFourierCoefficient (P : ℝ) (k : Index → ℤ)
    (f : CoordinateSpace → F) : F :=
  ((2 * P) ^ 4)⁻¹ • ∫ y in spatialFourierCube P,
    Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) • f y

/-- A supported profile has the literal whole-space Fourier-integral
representation of the same coefficient. -/
theorem spatial_cube_fourier_coefficient_eq_fourier (P : ℝ) (k : Index → ℤ)
    (f : CoordinateSpace → F) (hz : ∀ y ∉ spatialFourierCube P, f y = 0) :
    spatialCubeFourierCoefficient P k f =
      ((2 * P) ^ 4)⁻¹ • 𝓕 f (spatialModeFrequency P k) := by
  unfold spatialCubeFourierCoefficient
  rw [Real.fourierIntegral_eq']
  simp only [spatialModePhase, ← neg_mul]
  apply congrArg (fun z : F => ((2 * P) ^ 4)⁻¹ • z)
  let g (y : CoordinateSpace) := Complex.exp
    ((↑(-2 * Real.pi * inner ℝ y (spatialModeFrequency P k)) : ℂ) * Complex.I) • f y
  have hg (y : CoordinateSpace) (hy : y ∉ spatialFourierCube P) : g y = 0 := by
    simp only [g, hz y hy, smul_zero]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hg

/-- The normalization makes the coefficient no larger than a uniform bound
on the original profile in the cube. -/
theorem spatial_cube_fourier_coefficient_norm_le (P : ℝ) (hP : 0 < P) (k : Index → ℤ)
    (f : CoordinateSpace → F) (M : ℝ)
    (hM : ∀ y ∈ spatialFourierCube P, ‖f y‖ ≤ M) :
    ‖spatialCubeFourierCoefficient P k f‖ ≤ M := by
  have volumeFinite : (volume : Measure CoordinateSpace) (spatialFourierCube P) < ⊤ := by
    rw [spatial_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have volumeReal : (volume : Measure CoordinateSpace).real (spatialFourierCube P) = (2 * P) ^ 4 := by
    rw [Measure.real, spatial_fourier_cube_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  have hI : ‖∫ y in spatialFourierCube P,
      Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) • f y‖ ≤ M * (2 * P) ^ 4 := by
    rw [← volumeReal]
    apply norm_setIntegral_le_of_norm_le_const_ae' volumeFinite
    exact Filter.Eventually.of_forall fun y hy => by
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hM y hy
  unfold spatialCubeFourierCoefficient
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 * P) ^ 4)⁻¹ * (M * (2 * P) ^ 4) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M := by
      rw [mul_comm M, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * P) ^ 4 ≠ 0), one_mul]

end Burnett.A03
