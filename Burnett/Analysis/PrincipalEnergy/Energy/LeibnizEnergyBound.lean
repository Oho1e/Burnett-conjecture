import Burnett.Analysis.PrincipalEnergy.Energy.WeakEnergyBound
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open scoped InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

def principal (D : ι → Op H) (R : ι → ι → Op H) : Op H :=
  ∑ a, ∑ b, R a b * D a * D b

def leibnizError (D : ι → Op H) (dR : ι → ι → Op H) : Op H :=
  ∑ a, ∑ b, dR a b * D b

/-- The nondivergence principal part differs from the negative of the
symmetric divergence operator by the first-order coefficient derivative. -/
theorem principal_eq_neg_divergence_sub_error (D : ι → Op H) (R dR : ι → ι → Op H)
    (hLeibniz : ∀ a b, D a * R a b = R a b * D a + dR a b) :
    principal D R = -divergence D R - leibnizError D dR := by
  simp only [principal, divergence, leibnizError, neg_neg, hLeibniz, add_mul, Finset.sum_add_distrib,
    add_sub_cancel_right]

/-- The first-order graph energy uses the value and all ordered derivatives. -/
def firstOrderEnergy (D : ι → Op H) (u : H) : ℝ :=
  Real.sqrt (‖u‖ ^ 2 + ∑ a, ‖D a u‖ ^ 2)

theorem norm_derivative_le_firstOrderEnergy (D : ι → Op H) (u : H) (a : ι) :
    ‖D a u‖ ≤ firstOrderEnergy D u := by
  classical
  have h := Finset.single_le_sum (f := fun b : ι => ‖D b u‖ ^ 2)
    (s := Finset.univ) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  exact Real.le_sqrt_of_sq_le (h.trans (le_add_of_nonneg_left (sq_nonneg ‖u‖)))

private theorem comm_divergence_eq_sum (D : ι → Op H) (R : ι → ι → Op H) (B : Op H) :
    comm (divergence D R) B = ∑ a, ∑ b, comm (-(D a * R a b * D b)) B := by
  simp only [comm, divergence, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_sub_distrib]

/-- The whole divergence energy is controlled by the sum of the bounds for
the three commutator terms. Constants do not depend on a second derivative. -/
theorem divergence_energy_bound (D : ι → Op H) (R : ι → ι → Op H) (B : Op H)
    (hD : ∀ a, IsSkew (D a)) (hB : B.IsSymmetric)
    (hR : ∀ a b x y, ⟪R a b x, y⟫_ℂ = ⟪x, R b a y⟫_ℂ)
    (u : H) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hm : ∀ a b v, ‖R a b v‖ ≤ A * ‖v‖)
    (hlip : ∀ a b v, ‖comm (R a b) B v‖ ≤ K * A * ‖v‖)
    (hdB : ∀ a, ‖comm (D a) B u‖ ≤ K * firstOrderEnergy D u) :
    |2 * (⟪B u, divergence D R u⟫_ℂ).im| ≤
      (Fintype.card ι : ℝ)^2 * (3 * K * A) * firstOrderEnergy D u ^ 2 := by
  let n := firstOrderEnergy D u
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  have hs : (divergence D R).IsSymmetric := divergence_isSymmetric D R hD hR
  rw [imaginary_energy_eq_commutator _ _ hs hB]
  have hp : (⟪u, Complex.I • comm (divergence D R) B u⟫_ℂ).re =
      -(⟪u, comm (divergence D R) B u⟫_ℂ).im := by
    simp [inner_smul_right, Complex.mul_re]
  rw [hp, abs_neg]
  apply (Complex.abs_im_le_norm _).trans
  rw [comm_divergence_eq_sum D R B]
  simp only [LinearMap.sum_apply, inner_sum]
  calc
    _ ≤ ∑ a, ∑ b, ‖⟪u, comm (-(D a * R a b * D b)) B u⟫_ℂ‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ι, ∑ _b : ι, (2 * A * K + K * A) * n^2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact weak_commutator_bound (D a) (R a b) (D b) B (hD a) hB u A K (K * A) n
        hA hK (mul_nonneg hK hA) hn (hm a b) (hlip a b)
        (norm_derivative_le_firstOrderEnergy D u a) (norm_derivative_le_firstOrderEnergy D u b)
        (hdB a) (hdB b)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The Leibniz remainder costs one derivative of the coefficient and one
derivative of the test, paired with the same first-order operator. -/
theorem leibniz_error_energy_bound (D : ι → Op H) (dR : ι → ι → Op H) (B : Op H)
    (u : H) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hm : ∀ a b v, ‖dR a b v‖ ≤ A * ‖v‖)
    (hBu : ‖B u‖ ≤ K * firstOrderEnergy D u) :
    |2 * (⟪B u, leibnizError D dR u⟫_ℂ).im| ≤
      (Fintype.card ι : ℝ)^2 * (2 * K * A) * firstOrderEnergy D u ^ 2 := by
  let n := firstOrderEnergy D u
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hInner : |(⟪B u, leibnizError D dR u⟫_ℂ).im| ≤
      (Fintype.card ι : ℝ)^2 * ((K * n) * (A * n)) := by
    apply (Complex.abs_im_le_norm _).trans
    simp only [leibnizError, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
    calc
      _ ≤ ∑ a, ∑ b, ‖⟪B u, dR a b (D b u)⟫_ℂ‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : ι, ∑ _b : ι, (K * n) * (A * n) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        exact mul_le_mul hBu ((hm _ _ _).trans
          (mul_le_mul_of_nonneg_left (norm_derivative_le_firstOrderEnergy D u b) hA))
          (norm_nonneg _) (mul_nonneg hK hn)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc
    _ ≤ 2 * ((Fintype.card ι : ℝ)^2 * ((K * n) * (A * n))) := by gcongr
    _ = _ := by dsimp [n]; ring

/-- The original nondivergence energy estimate under the precise first-order
mapping and Lipschitz commutator bounds on the common test space. -/
theorem principal_energy_bound (D : ι → Op H) (R dR : ι → ι → Op H) (B : Op H)
    (hD : ∀ a, IsSkew (D a)) (hB : B.IsSymmetric)
    (hR : ∀ a b x y, ⟪R a b x, y⟫_ℂ = ⟪x, R b a y⟫_ℂ)
    (hLeibniz : ∀ a b, D a * R a b = R a b * D a + dR a b)
    (u : H) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hm : ∀ a b v, ‖R a b v‖ ≤ A * ‖v‖) (hdm : ∀ a b v, ‖dR a b v‖ ≤ A * ‖v‖)
    (hlip : ∀ a b v, ‖comm (R a b) B v‖ ≤ K * A * ‖v‖)
    (hdB : ∀ a, ‖comm (D a) B u‖ ≤ K * firstOrderEnergy D u)
    (hBu : ‖B u‖ ≤ K * firstOrderEnergy D u) :
    |2 * (⟪B u, principal D R u⟫_ℂ).im| ≤
      (5 * (Fintype.card ι : ℝ)^2 * K) * A * firstOrderEnergy D u ^ 2 := by
  rw [principal_eq_neg_divergence_sub_error D R dR hLeibniz]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, inner_sub_right, inner_neg_right,
    Complex.sub_im, Complex.neg_im, mul_sub, mul_neg]
  calc
    _ ≤ |-(2 * (⟪B u, divergence D R u⟫_ℂ).im)| +
        |2 * (⟪B u, leibnizError D dR u⟫_ℂ).im| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_neg]
      have h := add_le_add (divergence_energy_bound D R B hD hB hR u A K hA hK hm hlip hdB)
        (leibniz_error_energy_bound D dR B u A K hA hK hdm hBu)
      convert h using 1
      ring

end Burnett.Analysis.SymmetricEnergy
