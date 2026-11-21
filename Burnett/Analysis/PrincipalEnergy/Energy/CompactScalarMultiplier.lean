import Burnett.Analysis.PrincipalEnergy.Energy.CompactSchwartzDomain
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalSmoothCoefficientL2

set_option autoImplicit false
set_option maxHeartbeats 5700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff ComplexConjugate BigOperators InnerProductSpace

/-- Multiplication by the original scalar coefficient preserves compact
Schwartz data without any support requirement on the coefficient. -/
def compactScalarMultiplier {ι : Type*} (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι where
  toFun f := ⟨fun i => smoothScalarSchwartzProduct r hr (f.val i) (f.property i), fun i => (f.property i).mul_left⟩
  map_add' f g := by
    apply Subtype.ext
    funext i
    ext x
    change r x * (f.val i x+g.val i x) = r x*f.val i x+r x*g.val i x
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext i
    ext x
    change r x*(c*f.val i x) = c*(r x*f.val i x)
    ring

@[simp] theorem compactScalarMultiplier_apply {ι : Type*} (r : Space → ℂ) (hr : ContDiff ℝ ∞ r)
    (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    (compactScalarMultiplier r hr f).val i x = r x*f.val i x := rfl

def scalarCoordinateDerivative (r : Space → ℂ) (b : Fin 4) (x : Space) : ℂ :=
  fderiv ℝ r x (coordinateDirection b)

theorem scalarCoordinateDerivative_smooth {r : Space → ℂ} (hr : ContDiff ℝ ∞ r) (b : Fin 4) :
    ContDiff ℝ ∞ (scalarCoordinateDerivative r b) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ r) := by
    rw [contDiff_iff_forall_nat_le]
    intro n _
    exact hr.fderiv_right (by exact_mod_cast (le_top : (n : ℕ∞)+1 ≤ ⊤))
  exact hd.clm_apply contDiff_const

theorem compactScalarMultiplier_leibniz {ι : Type*} [Fintype ι]
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (b : Fin 4) :
    let D := compactTransportOp (compactComponentDerivative (ι := ι) b)
    let R := compactTransportOp (compactScalarMultiplier r hr)
    let dR := compactTransportOp (compactScalarMultiplier (scalarCoordinateDerivative r b)
      (scalarCoordinateDerivative_smooth hr b))
    D*R = R*D+dR := by
  intro D R dR
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  dsimp only [D, R, dR]
  simp only [Module.End.mul_apply, LinearMap.add_apply, compactTransportOp_apply, ← map_add]
  apply congrArg (compactMatrixTestEquiv ι)
  apply Subtype.ext
  funext i
  ext x
  change fderiv ℝ (fun y => r y*f.val i y) x (coordinateDirection b) =
    r x * (fderiv ℝ (f.val i : Space → ℂ) x (coordinateDirection b)) +
      (fderiv ℝ r x (coordinateDirection b))*f.val i x
  rw [fderiv_fun_mul (((hr.differentiable (by simp)) x)) (f.val i).differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem compactScalarMultiplier_adjoints {ι : Type*} [Fintype ι]
    (r s : Space → ℂ) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) (h : ∀ x, conj (r x) = s x)
    (u v : CompactMatrixTest ι) :
    ⟪compactTransportOp (compactScalarMultiplier r hr) u, v⟫_ℂ =
      ⟪u, compactTransportOp (compactScalarMultiplier s hs) v⟫_ℂ := by
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  obtain ⟨g, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner, compactScalarMultiplier_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, h x]
  ring

private theorem schwartz_norm_sq_toLp_eq_integral (f : SchwartzMap Space ℂ) :
    ‖f.toLp 2 volume‖^2 = ∫ x, ‖f x‖^2 := by
  rw [l2_norm_sq_integral]
  exact integral_congr_ae ((f.coeFn_toLp 2 volume).fun_comp fun z => ‖z‖^2)

theorem compactScalarMultiplier_norm_le {ι : Type*} [Fintype ι]
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (A : ℝ) (hA : 0 ≤ A)
    (hSup : ∀ x, ‖r x‖ ≤ A) (v : CompactMatrixTest ι) :
    ‖compactTransportOp (compactScalarMultiplier r hr) v‖ ≤ A*‖v‖ := by
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_norm]
  unfold matrixSchwartzL2Norm
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  simp only [PiLp.toLp_apply]
  apply Finset.sum_le_sum
  intro i _
  let g := (compactScalarMultiplier r hr f).val i
  let u := f.val i
  change ‖g.toLp 2 volume‖^2 ≤ A^2 * ‖u.toLp 2 volume‖^2
  rw [schwartz_norm_sq_toLp_eq_integral, schwartz_norm_sq_toLp_eq_integral, ← integral_const_mul]
  apply integral_mono ((g.memLp 2 volume).integrable_norm_pow (by decide : (2:ℕ)≠0))
    (((u.memLp 2 volume).integrable_norm_pow (by decide : (2:ℕ)≠0)).const_mul _)
  intro x
  change ‖r x*u x‖^2 ≤ A^2*‖u x‖^2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hSup x) _) (sq_nonneg _)

end Burnett.Analysis.CarlesonEmbedding
