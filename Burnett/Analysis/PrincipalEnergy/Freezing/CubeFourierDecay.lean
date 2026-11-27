import Burnett.Analysis.SpatialFreezing.FixedCubeFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Complex Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped FourierTransform ContDiff RealInnerProductSpace BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem fourier_pderiv_banach (f : SchwartzMap CoordinateSpace F) (v ξ : CoordinateSpace) :
    𝓕 (SchwartzMap.pderivCLM ℂ v f : CoordinateSpace → F) ξ =
      ((2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ)) • 𝓕 (f : CoordinateSpace → F) ξ := by
  have hd := congrFun (Real.fourierIntegral_fderiv f.integrable f.differentiable
    (SchwartzMap.fderivCLM ℂ f).integrable) ξ
  have hv := congrArg (fun L : CoordinateSpace →L[ℝ] F => L v) hd
  have hi : Integrable (fderiv ℝ (f : CoordinateSpace → F)) := (SchwartzMap.fderivCLM ℂ f).integrable
  change (𝓕 (fderiv ℝ (f : CoordinateSpace → F)) ξ) v = _ at hv
  rw [Real.fourierIntegral_continuousLinearMap_apply (f := fderiv ℝ (f : CoordinateSpace → F)) hi] at hv
  have hsame : 𝓕 (SchwartzMap.pderivCLM ℂ v f : CoordinateSpace → F) ξ =
      (-(2 * Real.pi * Complex.I) : ℂ) • (-inner ℝ ξ v) • 𝓕 (f : CoordinateSpace → F) ξ := by
    simpa only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
      innerSL_apply] using hv
  rw [hsame, ← coe_smul, Complex.ofReal_neg, smul_smul, neg_mul, mul_neg, neg_neg]

/-- Repeat the derivative in one actual coordinate direction. -/
def spatialCoordinateDerivative (j : Index) (n : ℕ) (f : SchwartzMap CoordinateSpace F) :
    SchwartzMap CoordinateSpace F :=
  SchwartzMap.iteratedPDeriv ℂ (fun _ : Fin n => EuclideanSpace.single j 1) f

def spatialModeDerivativeFactor (P : ℝ) (k : Index → ℤ) (j : Index) : ℂ :=
  (2 * Real.pi * Complex.I) * (inner ℝ (spatialModeFrequency P k) (EuclideanSpace.single j 1) : ℂ)

def spatialModeRate (P : ℝ) : ℝ := (2 * Real.pi) / (2 * P)

private theorem mode_factor_norm (P : ℝ) (hP : 0 < P) (k : Index → ℤ) (j : Index) :
    ‖spatialModeDerivativeFactor P k j‖ = spatialModeRate P * |(k j : ℝ)| := by
  have hj : (spatialModeFrequency P k) j = (2 * P)⁻¹ * (k j : ℝ) := rfl
  have hInv : 0 ≤ (2 * P)⁻¹ := by positivity
  have hInner : inner ℝ (spatialModeFrequency P k) (EuclideanSpace.single j 1) =
      (2 * P)⁻¹ * (k j : ℝ) := by
    rw [EuclideanSpace.inner_single_right]
    simpa only [conj_trivial, one_mul] using hj
  unfold spatialModeDerivativeFactor
  rw [hInner]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hInv, show ‖(2 : ℂ)‖ = 2 by norm_num]
  simp only [spatialModeRate, div_eq_mul_inv, mul_assoc]

private theorem fourier_coordinate_repeated (f : SchwartzMap CoordinateSpace F) (P : ℝ)
    (k : Index → ℤ) (j : Index) (n : ℕ) :
    𝓕 (spatialCoordinateDerivative j n f : CoordinateSpace → F) (spatialModeFrequency P k) =
      spatialModeDerivativeFactor P k j ^ n • 𝓕 (f : CoordinateSpace → F) (spatialModeFrequency P k) := by
  induction n with
  | zero => simp [spatialCoordinateDerivative]
  | succ n ih =>
    change 𝓕 (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) (spatialCoordinateDerivative j n f) :
      CoordinateSpace → F) (spatialModeFrequency P k) = _
    rw [fourier_pderiv_banach, ih]
    change spatialModeDerivativeFactor P k j •
      spatialModeDerivativeFactor P k j ^ n • 𝓕 (f : CoordinateSpace → F) (spatialModeFrequency P k) = _
    rw [smul_smul, pow_succ, mul_comm]

private theorem coord_deriv_norm_le (j : Index) (n : ℕ) (f : SchwartzMap CoordinateSpace F)
    (y : CoordinateSpace) :
    ‖spatialCoordinateDerivative j n f y‖ ≤ ‖iteratedFDeriv ℝ n (f : CoordinateSpace → F) y‖ := by
  unfold spatialCoordinateDerivative
  rw [SchwartzMap.iteratedPDeriv_eq_iteratedFDeriv]
  simpa using (iteratedFDeriv ℝ n (f : CoordinateSpace → F) y).le_opNorm
    (fun _ : Fin n => EuclideanSpace.single j (1 : ℝ))

/-- Repeated integration by parts in the exact cube coefficient. The
derivative stays supported in the same physical cube. -/
theorem spatial_cube_fourier_coefficient_repeated_ibp (f : SchwartzMap CoordinateSpace F)
    (P : ℝ) (k : Index → ℤ) (j : Index) (n : ℕ)
    (hSupport : tsupport (f : CoordinateSpace → F) ⊆ spatialFourierCube P) :
    spatialCubeFourierCoefficient P k (spatialCoordinateDerivative j n f) =
      spatialModeDerivativeFactor P k j ^ n • spatialCubeFourierCoefficient P k f := by
  have hf (y : CoordinateSpace) (hy : y ∉ spatialFourierCube P) : f y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hSupport h))
  have hd (y : CoordinateSpace) (hy : y ∉ spatialFourierCube P) : spatialCoordinateDerivative j n f y = 0 := by
    have hZero : iteratedFDeriv ℝ n (f : CoordinateSpace → F) y = 0 :=
      Function.notMem_support.mp (fun h => hy (hSupport (support_iteratedFDeriv_subset n h)))
    rw [spatialCoordinateDerivative, SchwartzMap.iteratedPDeriv_eq_iteratedFDeriv, hZero]
    rfl
  rw [spatial_cube_fourier_coefficient_eq_fourier P k _ hd,
    spatial_cube_fourier_coefficient_eq_fourier P k _ hf, fourier_coordinate_repeated]
  exact smul_comm _ _ _

private theorem exists_large_coordinate (k : Index → ℤ) (hk : k ≠ 0) :
    ∃ j : Index, 1 ≤ |(k j : ℝ)| ∧ ‖spatialLatticeVector k‖ ≤ 2 * |(k j : ℝ)| := by
  have nonzero : ∃ i : Index, k i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hk (funext hn)
  obtain ⟨i, hi⟩ := nonzero
  have integerLower : (1 : ℤ) ≤ |k i| := by
    have positive := abs_pos.mpr hi
    omega
  have realLower : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast integerLower
  obtain ⟨j, _, largest⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Index) (fun j => |(k j : ℝ)|) Finset.univ_nonempty
  refine ⟨j, realLower.trans (largest i (Finset.mem_univ _)), ?_⟩
  have hsq : ‖spatialLatticeVector k‖ ^ 2 ≤ 4 * |(k j : ℝ)| ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Index, |(k j : ℝ)| ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        change ‖(k v : ℝ)‖ ^ 2 ≤ _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (largest v hv) _
      _ = _ := by norm_num [Finset.sum_const, nsmul_eq_mul, Index]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hsq]

/-- The polynomial decay estimate in the Euclidean lattice norm, with the
zero mode controlled by the original profile bound. -/
theorem spatial_cube_fourier_coefficient_polynomial_decay (f : SchwartzMap CoordinateSpace F)
    (P : ℝ) (hP : 0 < P) (n : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hSupport : tsupport (f : CoordinateSpace → F) ⊆ spatialFourierCube P)
    (value : ∀ y ∈ spatialFourierCube P, ‖f y‖ ≤ M)
    (jet : ∀ y ∈ spatialFourierCube P, ‖iteratedFDeriv ℝ n (f : CoordinateSpace → F) y‖ ≤ M)
    (k : Index → ℤ) :
    ‖spatialCubeFourierCoefficient P k f‖ ≤
      (max 1 ((3 / spatialModeRate P) ^ n) * M) / (1 + ‖spatialLatticeVector k‖) ^ n := by
  have hRate : 0 < spatialModeRate P := by unfold spatialModeRate; positivity
  let C := max 1 ((3 / spatialModeRate P) ^ n)
  have hv := spatial_cube_fourier_coefficient_norm_le P hP k f M value
  by_cases hk : k = 0
  · subst k
    have hZero : spatialLatticeVector (0 : Index → ℤ) = 0 := by
      ext j
      simp [spatialLatticeVector]
    rw [hZero, norm_zero, add_zero, one_pow, div_one]
    refine hv.trans ?_
    calc
      M = (1 : ℝ) * M := (one_mul M).symm
      _ ≤ max 1 ((3 / spatialModeRate P) ^ n) * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  · obtain ⟨j, hOne, hLen⟩ := exists_large_coordinate k hk
    let A := spatialModeRate P * |(k j : ℝ)|
    let D := 3 / spatialModeRate P
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have hInt := spatial_cube_fourier_coefficient_norm_le P hP k (spatialCoordinateDerivative j n f) M
      (fun y hy => (coord_deriv_norm_le j n f y).trans (jet y hy))
    rw [spatial_cube_fourier_coefficient_repeated_ibp f P k j n hSupport, norm_smul, norm_pow,
      mode_factor_norm P hP] at hInt
    have hLen' : 1 + ‖spatialLatticeVector k‖ ≤ D * A := by
      have eq : D * A = 3 * |(k j : ℝ)| := by
        dsimp only [D, A]
        rw [← mul_assoc, div_mul_cancel₀ _ hRate.ne']
      rw [eq]
      linarith
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖spatialLatticeVector k‖) ^ n)).mpr
    calc
      _ ≤ ‖spatialCubeFourierCoefficient P k f‖ * (D * A) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLen' _) (norm_nonneg _)
      _ = D ^ n * (A ^ n * ‖spatialCubeFourierCoefficient P k f‖) := by rw [mul_pow]; ring
      _ ≤ D ^ n * M := mul_le_mul_of_nonneg_left hInt (pow_nonneg hD _)
      _ ≤ C * M := mul_le_mul_of_nonneg_right (le_max_right _ _) hM

end Burnett.A03
