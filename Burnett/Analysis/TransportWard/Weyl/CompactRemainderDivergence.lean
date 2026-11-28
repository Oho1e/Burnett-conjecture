import Burnett.Analysis.PrincipalEnergy.Energy.ActualMatrixPrincipalEnergy

/-! The divergence and drift of a matrix coefficient on the compact Schwartz domain. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.V03

open Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.SymmetricEnergy
  (Op comm principal divergence leibnizError coordinateDirection firstOrderEnergy)
open scoped BigOperators ComplexConjugate ContDiff InnerProductSpace

variable {ι : Type*} [Fintype ι]

abbrev RemainderArray (ι : Type*) := Fin 4 → Fin 4 → ι → ι → Space → ℂ

/-- Coefficient multiplication on the actual common compact test domain. -/
def remainderCoefficientOp (A : RemainderArray ι) (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (a b : Fin 4) : Op (CompactMatrixTest ι) :=
  compactTransportOp (compactFiniteMultiplier (A a b) (hA a b))

/-- Multiplication by the actual coefficient derivative in the divergence slot. -/
def remainderDerivativeOp (A : RemainderArray ι) (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (a b : Fin 4) : Op (CompactMatrixTest ι) :=
  compactTransportOp (compactFiniteMultiplier (fun i j => scalarCoordinateDerivative (A a b i j) a)
    (fun i j => scalarCoordinateDerivative_smooth (hA a b i j) a))

/-- Skew coordinate differentiation and symmetry under the two combined slots
make the actual divergence operator formally self-adjoint. -/
theorem compactRemainderDivergence_isSymmetric (A : RemainderArray ι)
    (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (hHerm : ∀ a b i j x, conj (A a b i j x) = A b a j i x) :
    (divergence compactMatrixCoordinatePartial (remainderCoefficientOp A hA)).IsSymmetric :=
  Burnett.Analysis.SymmetricEnergy.divergence_isSymmetric _ _
    compactMatrixDerivative_isSkew (fun a b =>
      compactFiniteMultiplier_adjoints (A a b) (A b a) (hA a b) (hA b a) (hHerm a b))

/-- The concrete nondivergence operator is the negative divergence minus the drift. -/
theorem compactRemainderPrincipal_eq (A : RemainderArray ι)
    (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j)) :
    principal compactMatrixCoordinatePartial (remainderCoefficientOp A hA) =
      -divergence compactMatrixCoordinatePartial (remainderCoefficientOp A hA) -
        leibnizError compactMatrixCoordinatePartial (remainderDerivativeOp A hA) :=
  Burnett.Analysis.SymmetricEnergy.principal_eq_neg_divergence_sub_error _ _ _
    (fun a b => compactFiniteMultiplier_leibniz (A a b) (hA a b) a)

/-- Read the principal operator and drift in the original ordered components. -/
theorem compactRemainderPrincipal_drift_components (A : RemainderArray ι)
    (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    let u := compactMatrixTestEquiv ι f
    ((compactMatrixTestEquiv ι).symm
        (principal compactMatrixCoordinatePartial (remainderCoefficientOp A hA) u)).val i x =
        compactFinitePrincipalField A f i x ∧
    ((compactMatrixTestEquiv ι).symm
        (leibnizError compactMatrixCoordinatePartial (remainderDerivativeOp A hA) u)).val i x =
      ∑ a, ∑ b, ∑ j, fderiv ℝ (A a b i j) x (coordinateDirection a) *
        fderiv ℝ (f.val j : Space → ℂ) x (coordinateDirection b) := by
  intro u
  let P : CompactSchwartzComponents ι :=
    ∑ a, ∑ b, compactFiniteMultiplier (A a b) (hA a b)
      (compactComponentDerivative a (compactComponentDerivative b f))
  let E : CompactSchwartzComponents ι :=
    ∑ a, ∑ b, compactFiniteMultiplier (fun i j => scalarCoordinateDerivative (A a b i j) a)
      (fun i j => scalarCoordinateDerivative_smooth (hA a b i j) a) (compactComponentDerivative b f)
  have hp : principal compactMatrixCoordinatePartial (remainderCoefficientOp A hA) u =
      compactMatrixTestEquiv ι P := by
    simp only [principal, remainderCoefficientOp, LinearMap.sum_apply, Module.End.mul_apply,
      compactMatrixCoordinatePartial, u, compactTransportOp_apply, P, map_sum]
  have he : leibnizError compactMatrixCoordinatePartial (remainderDerivativeOp A hA) u =
      compactMatrixTestEquiv ι E := by
    simp only [leibnizError, remainderDerivativeOp, LinearMap.sum_apply, Module.End.mul_apply,
      compactMatrixCoordinatePartial, u, compactTransportOp_apply, E, map_sum]
  rw [hp, he, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  constructor
  · change SchwartzMap.delta ℂ ℂ x
      (LinearMap.proj (R := ℂ) i ((compactSchwartzComponents ι).subtype P)) = _
    simp only [P, map_sum, LinearMap.proj_apply, Submodule.subtype_apply, SchwartzMap.delta_apply,
      compactFiniteMultiplier_apply, compactFinitePrincipalField]
    rfl
  · change SchwartzMap.delta ℂ ℂ x
      (LinearMap.proj (R := ℂ) i ((compactSchwartzComponents ι).subtype E)) = _
    simp only [E, map_sum, LinearMap.proj_apply, Submodule.subtype_apply, SchwartzMap.delta_apply,
      compactFiniteMultiplier_apply]
    rfl

/-- The manuscript's pairing reads as `inner (B u) (P u)` in Lean.
The commutator is `L B - B L`, where `L = -∂(A∂)`. -/
theorem imaginary_compactRemainder_eq (A : RemainderArray ι)
    (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (hHerm : ∀ a b i j x, conj (A a b i j x) = A b a j i x)
    (B : Op (CompactMatrixTest ι)) (hB : B.IsSymmetric) (u : CompactMatrixTest ι) :
    let D := compactMatrixCoordinatePartial (ι := ι)
    let R := remainderCoefficientOp A hA
    let dR := remainderDerivativeOp A hA
    let L := divergence D R
    2 * (⟪B u, principal D R u⟫_ℂ).im =
      -(⟪u, Complex.I • comm L B u⟫_ℂ).re - 2 * (⟪B u, leibnizError D dR u⟫_ℂ).im := by
  intro D R dR L
  rw [show principal D R = -L - leibnizError D dR from compactRemainderPrincipal_eq A hA]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, inner_sub_right, inner_neg_right,
    Complex.sub_im, Complex.neg_im, mul_sub, mul_neg]
  rw [Burnett.Analysis.SymmetricEnergy.imaginary_energy_eq_commutator L B
    (compactRemainderDivergence_isSymmetric A hA hHerm) hB u]

/-- The drift needs a bound for the first coefficient derivative and the
order-one mapping bound for the very same test operator. -/
theorem imaginary_compactRemainder_drift_bound (A : RemainderArray ι)
    (hA : ∀ a b i j, ContDiff ℝ ∞ (A a b i j))
    (J K : ℝ) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hdA : ∀ a b i j x, ‖fderiv ℝ (A a b i j) x‖ ≤ J)
    (B : Op (CompactMatrixTest ι)) (u : CompactMatrixTest ι)
    (hB : ‖B u‖ ≤ K * firstOrderEnergy compactMatrixCoordinatePartial u) :
    |2 * (⟪B u, leibnizError compactMatrixCoordinatePartial (remainderDerivativeOp A hA) u⟫_ℂ).im| ≤
      (16 * (Fintype.card ι : ℝ)^2 * (2 * K * J)) *
        (firstOrderEnergy compactMatrixCoordinatePartial u)^2 := by
  let M := (Fintype.card ι : ℝ)^2 * J
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD (a b : Fin 4) (v : CompactMatrixTest ι) :
      ‖remainderDerivativeOp A hA a b v‖ ≤ M * ‖v‖ := by
    refine compactFiniteMultiplier_norm_le _ _ J hJ (fun i j x => ?_) v
    change ‖fderiv ℝ (A a b i j) x (coordinateDirection a)‖ ≤ J
    have hv : ‖coordinateDirection a‖ = 1 := by
      simp only [coordinateDirection, EuclideanSpace.norm_single, norm_one]
    exact ((fderiv ℝ (A a b i j) x).le_opNorm (coordinateDirection a)).trans
      (by rw [hv, mul_one]; exact hdA a b i j x)
  have h := Burnett.Analysis.SymmetricEnergy.leibniz_error_energy_bound
    compactMatrixCoordinatePartial (remainderDerivativeOp A hA) B u M K hM hK hD hB
  simp only [Fintype.card_fin, Nat.cast_ofNat, show (4 : ℝ)^2 = 16 by norm_num, M] at h
  convert h using 1
  ring

end Burnett.V03
