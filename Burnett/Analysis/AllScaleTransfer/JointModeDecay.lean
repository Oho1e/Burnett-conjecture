import Burnett.Analysis.AllScaleTransfer.JointCubeDecay
import Burnett.Analysis.AllScaleTransfer.EightDimensionalModeSummation
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.A05.BoxFourier

open MeasureTheory Set Burnett.A03
open scoped ContDiff RealInnerProductSpace

abbrev Frequency := EuclideanSpace ℝ (Fin 4)

def joinedInputs (ζ υ : Frequency) : BoxSpace :=
  WithLp.toLp 2 (Sum.elim (fun i => ζ i) (fun i => υ i))

def firstInput (z : BoxSpace) : Frequency := WithLp.toLp 2 (fun i => z (Sum.inl i))

def secondInput (z : BoxSpace) : Frequency := WithLp.toLp 2 (fun i => z (Sum.inr i))

@[simp] theorem firstInput_joined (ζ υ : Frequency) : firstInput (joinedInputs ζ υ) = ζ := by
  ext i
  rfl

@[simp] theorem secondInput_joined (ζ υ : Frequency) : secondInput (joinedInputs ζ υ) = υ := by
  ext i
  rfl

theorem joinedInputs_split (z : BoxSpace) : joinedInputs (firstInput z) (secondInput z) = z := by
  ext i
  cases i <;> rfl

/-- The lattice of the box is exactly the pair of original four-dimensional modes. -/
def modeIndex : FourierModePair ≃ (BoxIndex → ℤ) where
  toFun ab := Sum.elim ab.1 ab.2
  invFun k := (k ∘ Sum.inl, k ∘ Sum.inr)
  left_inv ab := Prod.ext (funext fun _ => rfl) (funext fun _ => rfl)
  right_inv k := funext fun i => by cases i <;> rfl

theorem boxLatticeVector_modeIndex (ab : FourierModePair) :
    boxLatticeVector (modeIndex ab) = modePairLatticeVector ab := by
  ext i
  cases i <;> rfl

theorem boxModePhase_joined (P : ℝ) (ab : FourierModePair) (ζ υ : Frequency) :
    boxModePhase P (modeIndex ab) (joinedInputs ζ υ) =
      spatialModePhase P ab.1 ζ + spatialModePhase P ab.2 υ := by
  have h :
      inner ℝ (joinedInputs ζ υ) (boxLatticeVector (modeIndex ab)) =
        inner ℝ ζ (spatialLatticeVector ab.1) + inner ℝ υ (spatialLatticeVector ab.2) := by
    change (∑ i : BoxIndex, (modeIndex ab i : ℝ) * (joinedInputs ζ υ) i) =
      (∑ i : Fin 4, (ab.1 i : ℝ) * ζ i) + ∑ i : Fin 4, (ab.2 i : ℝ) * υ i
    rw [Fintype.sum_sum_type]
    rfl
  simp only [boxModePhase, spatialModePhase, boxModeFrequency, spatialModeFrequency,
    real_inner_smul_right, h]
  ring

def separatedBoxMode (P : ℝ) (ab : FourierModePair) (z : BoxSpace) : ℂ :=
  Complex.exp ((spatialModePhase P ab.1 (firstInput z) : ℂ) * Complex.I) *
    Complex.exp ((spatialModePhase P ab.2 (secondInput z) : ℂ) * Complex.I)

theorem box_phase_exp_eq_separated (P : ℝ) (ab : FourierModePair) (z : BoxSpace) :
    Complex.exp ((boxModePhase P (modeIndex ab) z : ℂ) * Complex.I) = separatedBoxMode P ab z := by
  conv_lhs => rw [← joinedInputs_split z, boxModePhase_joined]
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add, separatedBoxMode]

theorem norm_separatedBoxMode (P : ℝ) (ab : FourierModePair) (z : BoxSpace) :
    ‖separatedBoxMode P ab z‖ = 1 := by
  simp only [separatedBoxMode, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem one_le_lattice_norm {k : BoxIndex → ℤ} (hk : boxLatticeVector k ≠ 0) :
    1 ≤ ‖boxLatticeVector k‖ := by
  have h : ∃ i, k i ≠ 0 := by
    by_contra! h
    apply hk
    ext i
    simp [boxLatticeVector, h i]
  obtain ⟨i, hi⟩ := h
  have hI : (1 : ℤ) ≤ |k i| := by
    have hPos := abs_pos.mpr hi
    omega
  have hR : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast hI
  exact hR.trans (by simpa only [boxLatticeVector, PiLp.toLp_apply, Real.norm_eq_abs]
    using PiLp.norm_apply_le (boxLatticeVector k) i)

/-- The two-mode coefficient envelope uses only the first forty jets. -/
theorem joint_cube_coefficient_pair_decay (P : ℝ) (hP : 0 < P) (f : BoxSpace → ℂ)
    (hSmooth : ContDiff ℝ 40 f) (hCompact : HasCompactSupport f)
    (hs : tsupport f ⊆ boxFourierCube P) (M : ℝ) (hM : 0 ≤ M)
    (bound : ∀ n ≤ 40, ∀ z ∈ boxFourierCube P, ‖iteratedFDeriv ℝ n f z‖ ≤ M)
    (ab : FourierModePair) :
    ‖boxCubeFourierCoefficient P (modeIndex ab) f‖ ≤ boxDecayConstant P * M * modePairDecay ab := by
  let c := boxCubeFourierCoefficient P (modeIndex ab) f
  let x := ‖spatialLatticeVector ab.1‖
  let y := ‖spatialLatticeVector ab.2‖
  let z := ‖boxLatticeVector (modeIndex ab)‖
  have square : z^2 = x^2 + y^2 := by
    dsimp only [z, x, y]
    rw [boxLatticeVector_modeIndex, modePairLatticeVector_norm_sq]
  by_cases hz : boxLatticeVector (modeIndex ab) = 0
  · have hz' : z = 0 := by simp [z, hz]
    have hx : x = 0 := by nlinarith only [square, hz', sq_nonneg y, norm_nonneg (spatialLatticeVector ab.1)]
    have hy : y = 0 := by nlinarith only [square, hz', sq_nonneg x, norm_nonneg (spatialLatticeVector ab.2)]
    have hc : ‖c‖ ≤ M := box_cube_fourier_coefficient_norm_le P hP _ f M
      (fun w hw => by simpa only [norm_iteratedFDeriv_zero] using bound 0 (by decide) w hw)
    have hC : M ≤ boxDecayConstant P * M := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 _) hM
    change ‖c‖ ≤ boxDecayConstant P * M * (1 / (1 + x + y)^40)
    simpa only [hx, hy, add_zero, one_pow, div_one, mul_one] using hc.trans hC
  · have hz1 : 1 ≤ z := one_le_lattice_norm hz
    have hxz : x ≤ z := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [square]; exact le_add_of_nonneg_right (sq_nonneg _))
    have hyz : y ≤ z := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [square]; exact le_add_of_nonneg_left (sq_nonneg _))
    have hp : 1 + x + y ≤ 3 * z := by linarith only [hz1, hxz, hyz]
    have hpos : 0 < 1 + x + y := by dsimp [x, y]; positivity
    change ‖c‖ ≤ boxDecayConstant P * M * (1 / (1 + x + y)^40)
    rw [mul_one_div]
    apply (le_div_iff₀ (pow_pos hpos _)).mpr
    calc
      _ ≤ ‖c‖ * (3 * z)^40 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hp _) (norm_nonneg _)
      _ = (3 : ℝ)^40 * (z^40 * ‖c‖) := by rw [mul_pow]; ring
      _ ≤ (3 : ℝ)^40 * (((2 * P)^40 * (2^40 * 41)) * M) :=
        mul_le_mul_of_nonneg_left
          (joint_cube_coefficient_norm_pow_le P hP f hSmooth hCompact hs M bound _) (by positivity)
      _ ≤ boxDecayConstant P * M := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right 1 _) hM

end Burnett.A05.BoxFourier
