import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A06

open MeasureTheory Set Metric
open scoped Pointwise BigOperators

abbrev RotationSpace := EuclideanSpace ℝ (Fin 4)
abbrev RoundSphere3 := sphere (0 : RotationSpace) 1

def roundSphere3Measure : Measure RoundSphere3 :=
  (volume : Measure RotationSpace).toSphere

private def axis (i : Fin 4) : RotationSpace := EuclideanSpace.single i 1

private def coordinate (i : Fin 4) : RotationSpace →ₗ[ℝ] ℝ :=
  (EuclideanSpace.proj i).toLinearMap

private def planeRotationLinear (i j : Fin 4) (t : ℝ) : RotationSpace →ₗ[ℝ] RotationSpace :=
  LinearMap.id +
    (((Real.cos t - 1) • coordinate i - Real.sin t • coordinate j).smulRight (axis i)) +
    ((Real.sin t • coordinate i + (Real.cos t - 1) • coordinate j).smulRight (axis j))

private theorem planeRotationLinear_apply (i j : Fin 4) (t : ℝ) (x : RotationSpace) :
    planeRotationLinear i j t x =
      x + ((Real.cos t - 1) * x i - Real.sin t * x j) • axis i +
        (Real.sin t * x i + (Real.cos t - 1) * x j) • axis j := rfl

private theorem planeRotationLinear_i {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RotationSpace) :
    (planeRotationLinear i j t x) i = Real.cos t * x i - Real.sin t * x j := by
  rw [planeRotationLinear_apply]
  simp [axis, EuclideanSpace.single_apply, hij]
  ring

private theorem planeRotationLinear_j {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RotationSpace) :
    (planeRotationLinear i j t x) j = Real.sin t * x i + Real.cos t * x j := by
  rw [planeRotationLinear_apply]
  simp [axis, EuclideanSpace.single_apply, Ne.symm hij]
  ring

private theorem planeRotationLinear_other {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j)
    (t : ℝ) (x : RotationSpace) : (planeRotationLinear i j t x) k = x k := by
  rw [planeRotationLinear_apply]
  simp [axis, EuclideanSpace.single_apply, hki, hkj]

private theorem planeRotationLinear_norm {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RotationSpace) :
    ‖planeRotationLinear i j t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  let rest := (Finset.univ.erase i).erase j
  have hs (z : RotationSpace) :
      (∑ k : Fin 4, z k ^ 2) = (∑ k ∈ rest, z k ^ 2) + z j ^ 2 + z i ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  have hr : (∑ k ∈ rest, (planeRotationLinear i j t x k) ^ 2) = ∑ k ∈ rest, x k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [planeRotationLinear_other (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp hk).1]
  rw [hs (planeRotationLinear i j t x), hs x, hr, planeRotationLinear_i hij, planeRotationLinear_j hij]
  calc
    _ = (∑ k ∈ rest, x k ^ 2) + (Real.sin t ^ 2 + Real.cos t ^ 2) * (x i ^ 2 + x j ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]; ring

/-- Ordinary rotation in the ordered coordinate plane, in the fixed ambient R⁴. -/
def planeRotation {i j : Fin 4} (hij : i ≠ j) (t : ℝ) : RotationSpace ≃ₗᵢ[ℝ] RotationSpace := by
  let f : RotationSpace →ₗᵢ[ℝ] RotationSpace :=
    ⟨planeRotationLinear i j t, planeRotationLinear_norm hij t⟩
  exact LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

theorem planeRotation_apply {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RotationSpace) :
    planeRotation hij t x =
      x + ((Real.cos t - 1) * x i - Real.sin t * x j) • axis i +
        (Real.sin t * x i + (Real.cos t - 1) * x j) • axis j :=
  planeRotationLinear_apply i j t x

@[simp] theorem planeRotation_zero {i j : Fin 4} (hij : i ≠ j) (x : RotationSpace) :
    planeRotation hij 0 x = x := by simp [planeRotation_apply]

def planeRotationGenerator (i j : Fin 4) (x : RotationSpace) : RotationSpace :=
  x i • axis j - x j • axis i

theorem planeRotationGenerator_eq (i j : Fin 4) (x : RotationSpace) :
    planeRotationGenerator i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1 := rfl

theorem continuous_planeRotationGenerator (i j : Fin 4) :
    Continuous (planeRotationGenerator i j) := by
  unfold planeRotationGenerator
  exact (((EuclideanSpace.proj i).continuous).smul continuous_const).sub
    (((EuclideanSpace.proj j).continuous).smul continuous_const)

/-- The derivative of the ambient rotation curve is the exact tangent
rotation generator applied after that same rotation. -/
theorem hasDerivAt_planeRotation {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RotationSpace) :
    HasDerivAt (fun u => planeRotation hij u x)
      (planeRotationGenerator i j (planeRotation hij t x)) t := by
  have h₁ : HasDerivAt (fun u : ℝ => (Real.cos u - 1) * x i - Real.sin u * x j)
      (-Real.sin t * x i - Real.cos t * x j) t :=
    (((Real.hasDerivAt_cos t).sub_const 1).mul_const (x i)).sub
      ((Real.hasDerivAt_sin t).mul_const (x j))
  have h₂ : HasDerivAt (fun u : ℝ => Real.sin u * x i + (Real.cos u - 1) * x j)
      (Real.cos t * x i + -Real.sin t * x j) t :=
    ((Real.hasDerivAt_sin t).mul_const (x i)).add (((Real.hasDerivAt_cos t).sub_const 1).mul_const (x j))
  have h := ((h₁.smul_const (axis i)).const_add x).add (h₂.smul_const (axis j))
  have hi : planeRotation hij t x i = Real.cos t * x i - Real.sin t * x j :=
    planeRotationLinear_i hij t x
  have hj : planeRotation hij t x j = Real.sin t * x i + Real.cos t * x j :=
    planeRotationLinear_j hij t x
  convert h using 1
  rw [planeRotationGenerator, hi, hj]
  module

private theorem maps_roundSphere3 (U : RotationSpace ≃ₗᵢ[ℝ] RotationSpace) (x : RoundSphere3) :
    U x ∈ sphere (0 : RotationSpace) 1 := by
  rw [mem_sphere_zero_iff_norm, U.norm_map]
  exact mem_sphere_zero_iff_norm.mp x.property

private def sphereIsometry (U : RotationSpace ≃ₗᵢ[ℝ] RotationSpace) : RoundSphere3 ≃ᵐ RoundSphere3 where
  toFun x := ⟨U x, maps_roundSphere3 U x⟩
  invFun x := ⟨U.symm x, maps_roundSphere3 U.symm x⟩
  left_inv x := Subtype.ext (U.symm_apply_apply x)
  right_inv x := Subtype.ext (U.apply_symm_apply x)
  measurable_toFun := (U.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (U.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

private theorem sphereIsometry_preserves_measure (U : RotationSpace ≃ₗᵢ[ℝ] RotationSpace) :
    MeasurePreserving (sphereIsometry U) roundSphere3Measure roundSphere3Measure := by
  refine ⟨(sphereIsometry U).measurable, ?_⟩
  ext s hs
  rw [MeasurableEquiv.map_apply, roundSphere3Measure,
    Measure.toSphere_apply' _ ((sphereIsometry U).measurable hs), Measure.toSphere_apply' _ hs]
  let cone (s : Set RoundSphere3) : Set RotationSpace := Ioo (0 : ℝ) 1 • ((↑) '' s)
  have eq : cone ((sphereIsometry U) ⁻¹' s) = U ⁻¹' cone s := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, h⟩
      exact ⟨r, hr, U u, ⟨sphereIsometry U u, hu, rfl⟩, by rw [← h, map_smul]⟩
    · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, h⟩
      refine ⟨r, hr, U.symm u, ⟨(sphereIsometry U).symm u, ?_, rfl⟩, ?_⟩
      · simpa only [mem_preimage, MeasurableEquiv.apply_symm_apply] using hu
      · apply U.injective
        rw [map_smul, U.apply_symm_apply]
        exact h
  have ambient (A : Set RotationSpace) : volume (U ⁻¹' A) = volume A := by
    have h := congrArg (fun μ : Measure RotationSpace => μ A) U.measurePreserving.map_eq
    change Measure.map (U.toMeasurableEquiv : RotationSpace → RotationSpace) volume A = volume A at h
    rw [U.toMeasurableEquiv.measurableEmbedding.map_apply] at h
    exact h
  change _ * volume (cone ((sphereIsometry U) ⁻¹' s)) = _ * volume (cone s)
  rw [eq, ambient]

/-- The actual round surface measure is invariant under the coordinate-plane rotations. -/
def rotateRoundSphere3 {i j : Fin 4} (hij : i ≠ j) (t : ℝ) : RoundSphere3 ≃ᵐ RoundSphere3 :=
  sphereIsometry (planeRotation hij t)

@[simp] theorem coe_rotateRoundSphere3 {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (x : RoundSphere3) :
    (rotateRoundSphere3 hij t x : RotationSpace) = planeRotation hij t x := rfl

theorem measurePreserving_rotateRoundSphere3 {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    MeasurePreserving (rotateRoundSphere3 hij t) roundSphere3Measure roundSphere3Measure :=
  sphereIsometry_preserves_measure _

theorem integral_rotateRoundSphere3 {i j : Fin 4} (hij : i ≠ j) (t : ℝ) (f : RoundSphere3 → ℝ) :
    (∫ x, f (rotateRoundSphere3 hij t x) ∂roundSphere3Measure) = ∫ x, f x ∂roundSphere3Measure :=
  (measurePreserving_rotateRoundSphere3 hij t).integral_comp' f

end Burnett.A06
