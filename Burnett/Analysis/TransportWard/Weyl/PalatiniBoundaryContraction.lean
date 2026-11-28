import Burnett.Analysis.TransportWard.Weyl.EHBoundaryContraction

/-! Metric compatibility in the weighted contraction of the Palatini divergence. -/

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

open private sum_triple_rotate inverseDensityDerivative_contracted from Burnett.Analysis.TransportWard.Weyl.EHBoundaryContraction

private theorem weighted_covariantDerivative_first (W : Mat) (Γ C : Connection) (J : ConnectionJet)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    (∑ b, ∑ c, W b c * (∑ a, covariantDerivative Γ C J a a b c)) =
      (∑ a, ∑ b, ∑ c, W b c * J a a b c) +
        ∑ a, ∑ b, ∑ c, inverseDensityDerivative W Γ a b c * C a b c := by
  have hJ : (∑ b, ∑ c, ∑ a, W b c * J a a b c) = ∑ a, ∑ b, ∑ c, W b c * J a a b c :=
    sum_triple_rotate _
  have hTrace (b c : Index) : (∑ a, ∑ e, W b c * (Γ a a e * C e b c)) =
      ∑ e, connectionTrace Γ e * W b c * C e b c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp only [connectionTrace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hΓ a a e]
    ring
  have hTraceSum :
      (∑ b, ∑ c, ∑ a, ∑ e, W b c * (Γ a a e * C e b c)) =
      ∑ a, ∑ b, ∑ c, connectionTrace Γ a * W b c * C a b c := by
    simp only [hTrace]
    exact sum_triple_rotate _
  have hSwapB :
      (∑ b, ∑ c, ∑ a, ∑ e, W b c * (Γ e a b * C a e c)) =
        ∑ a, ∑ b, ∑ c, ∑ e, (Γ b a e * W e c) * C a b c := by
    rw [sum_triple_rotate (fun a b c => ∑ e, W b c * (Γ e a b * C a e c))]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = ∑ b, ∑ e, ∑ c, W b c * (Γ e a b * C a e c) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ e, ∑ b, ∑ c, W b c * (Γ e a b * C a e c) := Finset.sum_comm
      _ = ∑ e, ∑ c, ∑ b, W b c * (Γ e a b * C a e c) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro e _
        ring
  have hSwapC :
      (∑ b, ∑ c, ∑ a, ∑ e, W b c * (Γ e a c * C a b e)) =
        ∑ a, ∑ b, ∑ c, ∑ e, (W b e * Γ c a e) * C a b c := by
    rw [sum_triple_rotate (fun a b c => ∑ e, W b c * (Γ e a c * C a b e))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  simp only [covariantDerivative, inverseDensityDerivative, sub_mul, mul_add, mul_sub, add_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hJ, hTraceSum, hSwapB, hSwapC]
  ring

private theorem trace_covariantDerivative (Γ C : Connection) (J : ConnectionJet) (d b : Index) :
    (∑ a, covariantDerivative Γ C J d a b a) =
      (∑ a, J d a b a) - ∑ e, Γ e d b * connectionTrace C e := by
  have hCancel : (∑ a, ∑ e, Γ a d e * C e b a) = ∑ a, ∑ e, Γ e d a * C a b e :=
    Finset.sum_comm
  have hTrace : (∑ a, ∑ e, Γ e d b * C a e a) = ∑ e, Γ e d b * connectionTrace C e := by
    rw [Finset.sum_comm]
    simp only [connectionTrace, Finset.mul_sum]
  simp only [covariantDerivative, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hCancel, hTrace]
  ring

private theorem weighted_covariantDerivative_trace (W : Mat) (Γ C : Connection) (J : ConnectionJet)
    (hW : IsSymmetricTensor W) (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    (∑ b, ∑ c, W b c * (∑ a, covariantDerivative Γ C J c a b a)) =
      (∑ a, ∑ b, W b a * (∑ e, J a e b e)) +
        ∑ a, ∑ b, inverseDensityDerivative W Γ a b a * connectionTrace C b := by
  have hJ : (∑ b, ∑ c, W b c * (∑ a, J c a b a)) = ∑ c, ∑ b, W b c * (∑ a, J c a b a) :=
    Finset.sum_comm
  have hCross : (∑ b, ∑ c, ∑ e, W b c * (Γ e c b * connectionTrace C e)) =
      ∑ e, contractedConnection W Γ e * connectionTrace C e := by
    rw [sum_triple_rotate (fun e b c => W b c * (Γ e c b * connectionTrace C e))]
    simp only [contractedConnection, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [hΓ e c b]
  have hWeightedTrace : (∑ a, ∑ b, inverseDensityDerivative W Γ a b a * connectionTrace C b) =
      -(∑ b, contractedConnection W Γ b * connectionTrace C b) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, inverseDensityDerivative_contracted W Γ hW hΓ,
      neg_mul, Finset.sum_neg_distrib]
  simp only [trace_covariantDerivative, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum] at *
  rw [hJ, hCross, hWeightedTrace]
  ring

/-- Exact contraction of Palatini's covariant divergence, in the order
needed for ordinary coordinate integration by parts with the density. -/
theorem weighted_covariantDivergenceDifference_eq (W : Mat) (Γ C : Connection) (J : ConnectionJet)
    (hW : IsSymmetricTensor W) (hΓ : ∀ a b c, Γ a b c = Γ a c b) :
    metricTrace W (covariantDivergenceDifference Γ C J) =
      ricciDerivativeContraction W J +
        ((∑ a, ∑ b, ∑ c, inverseDensityDerivative W Γ a b c * C a b c) -
          ∑ a, ∑ b, inverseDensityDerivative W Γ a b a * connectionTrace C b) := by
  unfold metricTrace covariantDivergenceDifference
  simp only [Finset.sum_sub_distrib, mul_sub]
  rw [weighted_covariantDerivative_first W Γ C J hΓ,
    weighted_covariantDerivative_trace W Γ C J hW hΓ, ricciDerivativeContraction]
  ring

end Burnett.V03.Palatini
