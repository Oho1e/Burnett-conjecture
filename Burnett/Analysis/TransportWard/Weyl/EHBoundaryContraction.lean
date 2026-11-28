import Burnett.Analysis.TransportWard.Weyl.EHSpatialVariation

/-! Ordered-index contractions in the Einstein–Hilbert boundary identity. -/

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V02.EinsteinHilbert

open Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

/-- Contract both lower connection indices with a symmetric contravariant density. -/
def contractedConnection (W : Mat) (Γ : Connection) (a : Index) : ℝ :=
  ∑ b, ∑ c, W b c * Γ a b c

/-- Derivative of the contravariant inverse density, in terms of the connection. -/
def inverseDensityDerivative (W : Mat) (Γ : Connection) (a b c : Index) : ℝ :=
  connectionTrace Γ a * W b c -
    ∑ e, (W b e * Γ c a e + Γ b a e * W e c)

private theorem sum_triple_rotate (f : Index → Index → Index → ℝ) :
    (∑ b, ∑ c, ∑ a, f a b c) = ∑ a, ∑ b, ∑ c, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem metricTrace_quadraticDifference (W : Mat) (Γ : Connection)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    metricTrace W (quadraticDifference Γ) =
      (∑ a, connectionTrace Γ a * contractedConnection W Γ a) -
      ∑ a, ∑ b, ∑ c, ∑ e, W b c * Γ a c e * Γ e b a := by
  have hFirst (b c : Index) :
      (∑ a, ∑ e, W b c * (Γ a a e * Γ e b c)) =
        ∑ e, connectionTrace Γ e * (W b c * Γ e b c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [connectionTrace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hΓ a a e]
    ring
  have hSecond :
      (∑ b, ∑ c, ∑ a, ∑ e, W b c * (Γ a c e * Γ e b a)) =
        ∑ a, ∑ b, ∑ c, ∑ e, W b c * Γ a c e * Γ e b a := by
    rw [sum_triple_rotate (fun a b c => ∑ e, W b c * (Γ a c e * Γ e b a))]
    simp only [mul_assoc]
  calc
    _ = (∑ b, ∑ c, ∑ a, connectionTrace Γ a * (W b c * Γ a b c)) -
        ∑ b, ∑ c, ∑ a, ∑ e, W b c * (Γ a c e * Γ e b a) := by
      simp only [metricTrace, quadraticDifference, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, hFirst]
    _ = _ := by
      rw [hSecond, sum_triple_rotate (fun a b c => connectionTrace Γ a * (W b c * Γ a b c))]
      simp only [contractedConnection, Finset.mul_sum]

private theorem exchange_quadratic_contractions (W : Mat) (Γ : Connection)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    (∑ a, ∑ b, ∑ c, ∑ e, (Γ b a e * W e c) * Γ a b c) =
      ∑ a, ∑ b, ∑ c, ∑ e, W b c * Γ a c e * Γ e b a := by
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ b, ∑ e, ∑ c, (Γ b a e * W e c) * Γ a b c :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e, ∑ b, ∑ c, (Γ b a e * W e c) * Γ a b c := Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ b, (Γ b a e * W e c) * Γ a b c :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro e _
      rw [hΓ e a b, hΓ a e c]
      ring

private theorem symmetric_quadratic_contractions (W : Mat) (Γ : Connection)
    (hW : IsSymmetricTensor W) (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    (∑ a, ∑ b, ∑ c, ∑ e, (W b e * Γ c a e) * Γ a b c) =
      ∑ a, ∑ b, ∑ c, ∑ e, (Γ b a e * W e c) * Γ a b c := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [hW c e, hΓ a c b]
  ring

private theorem inverseDensityDerivative_contracted (W : Mat) (Γ : Connection)
    (hW : IsSymmetricTensor W) (hΓ : ∀ a b c, Γ a b c = Γ a c b) (b : Index) :
    (∑ a, inverseDensityDerivative W Γ a b a) = -contractedConnection W Γ b := by
  have hTrace : (∑ a, ∑ e, W b e * Γ a a e) = ∑ a, connectionTrace Γ a * W b a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp only [connectionTrace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [hΓ e e a, mul_comm]
  have hContract : (∑ a, ∑ e, Γ b a e * W e a) = contractedConnection W Γ b := by
    unfold contractedConnection
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro e _
    rw [hW e a, mul_comm]
  simp only [inverseDensityDerivative, Finset.sum_sub_distrib, Finset.sum_add_distrib, hTrace, hContract]
  ring

/-- The derivative of the volume-weighted inverse in the boundary product
contributes twice the signed ΓΓ contraction. -/
theorem inverseDensityDerivative_boundary_contraction (W : Mat) (Γ : Connection)
    (hW : IsSymmetricTensor W) (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    (∑ a, ∑ b, ∑ c, inverseDensityDerivative W Γ a b c * Γ a b c) -
      (∑ a, ∑ b, inverseDensityDerivative W Γ a b a * connectionTrace Γ b) =
       2 * metricTrace W (quadraticDifference Γ) := by
  have hFirst :
      (∑ a, ∑ b, ∑ c, inverseDensityDerivative W Γ a b c * Γ a b c) =
        (∑ a, connectionTrace Γ a * contractedConnection W Γ a) -
        ((∑ a, ∑ b, ∑ c, ∑ e, W b c * Γ a c e * Γ e b a) +
          (∑ a, ∑ b, ∑ c, ∑ e, W b c * Γ a c e * Γ e b a)) := by
    simp only [inverseDensityDerivative, sub_mul, Finset.sum_mul, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, contractedConnection, Finset.mul_sum]
    rw [symmetric_quadratic_contractions W Γ hW hΓ, exchange_quadratic_contractions W Γ hΓ]
    simp only [mul_assoc]
  have hSecond :
      (∑ a, ∑ b, inverseDensityDerivative W Γ a b a * connectionTrace Γ b) =
        -(∑ a, connectionTrace Γ a * contractedConnection W Γ a) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, inverseDensityDerivative_contracted W Γ hW hΓ,
      neg_mul, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hFirst, hSecond, metricTrace_quadraticDifference W Γ hΓ]
  ring

/-- The derivative part of the Ricci scalar written in boundary divergence order. -/
def ricciDerivativeContraction (W : Mat) (J : ConnectionJet) : ℝ :=
  (∑ a, ∑ b, ∑ c, W b c * J a a b c) -
    ∑ a, ∑ b, W b a * (∑ e, J a e b e)

theorem metricTrace_ricci_eq_derivative_add_quadratic (W : Mat) (Γ : Connection)
    (J : ConnectionJet) :
    metricTrace W (ricci Γ J) =
      ricciDerivativeContraction W J + metricTrace W (quadraticDifference Γ) := by
  have hFirst :
      (∑ b, ∑ c, ∑ a, W b c * J a a b c) = ∑ a, ∑ b, ∑ c, W b c * J a a b c :=
    sum_triple_rotate _
  have hSecond :
      (∑ b, ∑ c, ∑ a, W b c * J c a b a) =
        ∑ a, ∑ b, W b a * (∑ e, J a e b e) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [ricciDerivativeContraction, metricTrace, ricci, quadraticDifference, mul_add, mul_sub,
    Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hFirst, hSecond]

end Burnett.V02.EinsteinHilbert
