import Burnett.Analysis.CubicEnergy.AngularHarmonics.RoundSphereRotationIntegration
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A06

open Set Filter Metric
open scoped BigOperators ContDiff Topology

private def sphereAxis (i : Fin 4) : RotationSpace := EuclideanSpace.single i 1

/-- The six unordered planes of the fixed ambient Euclidean four-space. -/
def rotationPairs : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}

theorem mem_rotationPairs (i j : Fin 4) : (i, j) ∈ rotationPairs ↔ i < j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem sum_rotationPairs {R : Type*} [AddCommMonoid R] (f : Fin 4 × Fin 4 → R) :
    (∑ p ∈ rotationPairs, f p) =
      f (0, 1) + f (0, 2) + f (0, 3) + f (1, 2) + f (1, 3) + f (2, 3) := by
  simp (disch := decide) [rotationPairs, Finset.sum_insert, add_assoc]

private theorem sum_four (f : Fin 4 → ℝ) :
    (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
  simp only [add_assoc]

private theorem expand_in_axes (x : RotationSpace) :
    x = x 0 • sphereAxis 0 + x 1 • sphereAxis 1 + x 2 • sphereAxis 2 + x 3 • sphereAxis 3 := by
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [sphereAxis, EuclideanSpace.single_apply]

private theorem rotation_generator_square {i j : Fin 4} (hij : i ≠ j) (x : RotationSpace) :
    planeRotationGenerator i j (planeRotationGenerator i j x) =
      -(x i) • sphereAxis i - x j • sphereAxis j := by
  have hi : planeRotationGenerator i j x i = -x j := by
    simp [planeRotationGenerator_eq, EuclideanSpace.single_apply, hij]
  have hj : planeRotationGenerator i j x j = x i := by
    simp [planeRotationGenerator_eq, EuclideanSpace.single_apply, Ne.symm hij]
  rw [planeRotationGenerator_eq i j (planeRotationGenerator i j x), hi, hj]
  change (-x j) • sphereAxis j - x i • sphereAxis i = -(x i) • sphereAxis i - x j • sphereAxis j
  module

private theorem rotation_generator_square_sum (x : RotationSpace) :
    (∑ p ∈ rotationPairs, planeRotationGenerator p.1 p.2 (planeRotationGenerator p.1 p.2 x)) =
      (-3 : ℝ) • x := by
  simp (disch := decide) only [sum_rotationPairs, rotation_generator_square]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [sphereAxis, EuclideanSpace.single_apply] <;> ring

private theorem rotation_hessian_sum (B : RotationSpace →L[ℝ] RotationSpace →L[ℝ] ℝ)
    (x : RotationSpace) :
    (∑ p ∈ rotationPairs, B (planeRotationGenerator p.1 p.2 x) (planeRotationGenerator p.1 p.2 x)) =
      ‖x‖ ^ 2 * (∑ i : Fin 4, B (sphereAxis i) (sphereAxis i)) - B x x := by
  have hxx := congrArg (fun y => B y y) (expand_in_axes x)
  change B x x = _ at hxx
  rw [sum_rotationPairs, hxx, EuclideanSpace.norm_sq_eq]
  simp only [planeRotationGenerator_eq, sphereAxis, map_sub, map_add, map_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Real.norm_eq_abs, sq_abs, sum_four]
  ring

private def generatorCLM (i j : Fin 4) : RotationSpace →L[ℝ] RotationSpace :=
  (EuclideanSpace.proj i).smulRight (sphereAxis j) - (EuclideanSpace.proj j).smulRight (sphereAxis i)

private theorem generatorCLM_apply (i j : Fin 4) (x : RotationSpace) :
    generatorCLM i j x = planeRotationGenerator i j x :=
  (planeRotationGenerator_eq i j x).symm

private theorem rotation_square_apply {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin 4) (x : RotationSpace) :
    planeRotationDerivative i j (planeRotationDerivative i j f) x =
      fderiv ℝ f x (planeRotationGenerator i j (planeRotationGenerator i j x)) +
        fderiv ℝ (fderiv ℝ f) x (planeRotationGenerator i j x) (planeRotationGenerator i j x) := by
  have differentiated : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have eq : planeRotationDerivative i j f = fun z => fderiv ℝ f z (generatorCLM i j z) := by
    funext z
    rw [planeRotationDerivative, generatorCLM_apply]
  change fderiv ℝ (planeRotationDerivative i j f) x (planeRotationGenerator i j x) = _
  rw [eq, fderiv_clm_apply (differentiated x) (generatorCLM i j).differentiableAt,
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    generatorCLM_apply]

private theorem laplacian_coordinate_trace (f : RotationSpace → ℝ) (x : RotationSpace) :
    InnerProductSpace.laplacian f x =
      ∑ i : Fin 4, fderiv ℝ (fderiv ℝ f) x (sphereAxis i) (sphereAxis i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 4) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply, sphereAxis]

/-- On ambient tests the sum of the six squares is the spherical Casimir. -/
def planeRotationCasimir (f : RotationSpace → ℝ) (x : RotationSpace) : ℝ :=
  ∑ p ∈ rotationPairs, planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 f) x

theorem planeRotationCasimir_ambient {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (x : RotationSpace) :
    planeRotationCasimir f x = ‖x‖ ^ 2 * InnerProductSpace.laplacian f x -
      fderiv ℝ (fderiv ℝ f) x x x - 3 * fderiv ℝ f x x := by
  unfold planeRotationCasimir
  simp_rw [rotation_square_apply hf]
  rw [Finset.sum_add_distrib, ← map_sum, rotation_generator_square_sum,
    map_smul, smul_eq_mul, rotation_hessian_sum, ← laplacian_coordinate_trace]
  ring

private theorem euler_first {f : RotationSpace → ℝ} (hf : Differentiable ℝ f) (l : ℕ)
    (hom : ∀ (t : ℝ), 0 < t → ∀ x, f (t • x) = t ^ l * f x) (x : RotationSpace) :
    fderiv ℝ f x x = (l : ℝ) * f x := by
  have ray : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa only [id, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const x
  have atRay : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f x x) 1 := by
    have h0 : HasFDerivAt f (fderiv ℝ f x) ((1 : ℝ) • x) := by
      simpa only [one_smul] using (hf x).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt 1 h0 ray
  have power : HasDerivAt (fun t : ℝ => t ^ l * f x) ((l : ℝ) * f x) 1 := by
    simpa only [one_pow, mul_one] using (hasDerivAt_pow l (1 : ℝ)).mul_const (f x)
  have near : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 (1 : ℝ)] fun t => t ^ l * f x := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hom t ht x
  exact atRay.unique (power.congr_of_eventuallyEq near)

private theorem euler_second {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f) (l : ℕ)
    (hom : ∀ (t : ℝ), 0 < t → ∀ x, f (t • x) = t ^ l * f x) (x : RotationSpace) :
    fderiv ℝ (fderiv ℝ f) x x x = (l : ℝ) * ((l : ℝ) - 1) * f x := by
  have d : Differentiable ℝ f := hf.differentiable (by norm_num)
  have d₂ : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have e := congrArg (fun g : RotationSpace → ℝ => fderiv ℝ g x x) (funext (euler_first d l hom))
  change fderiv ℝ (fun z => fderiv ℝ f z (id z)) x x =
    fderiv ℝ (fun z => (l : ℝ) * f z) x x at e
  rw [fderiv_clm_apply (d₂ x) differentiableAt_id, fderiv_id, fderiv_const_mul (d x)] at e
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, id_eq, smul_eq_mul,
    euler_first d l hom x] at e
  linarith only [e]

/-- Euler's identities for a positive-dilation homogeneous C² test remove
the two radial derivatives from the ambient Casimir. -/
theorem planeRotationCasimir_homogeneous {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f) (l : ℕ)
    (hom : ∀ (t : ℝ), 0 < t → ∀ x, f (t • x) = t ^ l * f x) (x : RotationSpace) :
    planeRotationCasimir f x = ‖x‖ ^ 2 * InnerProductSpace.laplacian f x -
      (l : ℝ) * ((l : ℝ) + 2) * f x := by
  rw [planeRotationCasimir_ambient hf, euler_second hf l hom, euler_first (hf.differentiable (by norm_num)) l hom]
  ring

theorem planeRotationCasimir_homogeneous_on_sphere {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f) (l : ℕ)
    (hom : ∀ (t : ℝ), 0 < t → ∀ x, f (t • x) = t ^ l * f x) (x : RoundSphere3) :
    planeRotationCasimir f x = InnerProductSpace.laplacian f x - (l : ℝ) * ((l : ℝ) + 2) * f x := by
  rw [planeRotationCasimir_homogeneous hf l hom, mem_sphere_zero_iff_norm.mp x.property, one_pow, one_mul]

/-- Actual homogeneous harmonic restrictions satisfy the round S³
rotation-Casimir eigenvalue identity. -/
theorem planeRotationCasimir_harmonic_on_sphere {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f) (l : ℕ)
    (hom : ∀ (t : ℝ), 0 < t → ∀ x, f (t • x) = t ^ l * f x)
    (harmonic : ∀ x : RotationSpace, InnerProductSpace.laplacian f x = 0) (x : RoundSphere3) :
    planeRotationCasimir f x = -((l : ℝ) * ((l : ℝ) + 2)) * f x := by
  rw [planeRotationCasimir_homogeneous_on_sphere hf l hom, harmonic, zero_sub, neg_mul]

end Burnett.A06
