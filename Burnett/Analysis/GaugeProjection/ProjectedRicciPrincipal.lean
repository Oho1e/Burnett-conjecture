import Burnett.Geometry.CurvatureDifference
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators

abbrev SecondMetricJet := Index → FirstJet

private def metricContraction (inv A : Tensor2) : ℝ :=
  ∑ a, ∑ b, inv a b * A a b

private theorem metricContraction_swap (inv : Tensor2) (hInv : IsSymmetricTensor inv)
    (A : Tensor2) :
    metricContraction inv (fun a b => A b a) = metricContraction inv A := by
  unfold metricContraction
  calc
    (∑ a, ∑ b, inv a b * A b a) = ∑ b, ∑ a, inv a b * A b a := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hInv b a]

/-- The covector obtained by lowering the contracted Christoffel symbol. -/
def loweredGaugeCovector (inv : Tensor2) (dg : FirstJet) (i : Index) : ℝ :=
  metricContraction inv (fun a b => dg a b i) - metricContraction inv (dg i) / 2

theorem loweredGaugeCovector_eq_contractedChristoffel
    (g inv : Tensor2) (dg : FirstJet) (hInv : IsSymmetricTensor inv)
    (hi : ∀ a b, (∑ j, g a j * inv j b) = if a = b then 1 else 0) (i : Index) :
    (∑ ρ, g i ρ * (∑ a, ∑ b, inv a b * christoffel inv dg ρ a b)) =
      loweredGaugeCovector inv dg i := by
  have hswap : (∑ a, ∑ b, inv a b * dg b a i) = ∑ a, ∑ b, inv a b * dg a b i :=
    metricContraction_swap inv hInv (fun a b => dg a b i)
  calc
    (∑ ρ, g i ρ * (∑ a, ∑ b, inv a b * christoffel inv dg ρ a b)) =
        ∑ a, ∑ ρ, ∑ b, g i ρ * (inv a b * christoffel inv dg ρ a b) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, inv a b * (∑ ρ, g i ρ * christoffel inv dg ρ a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    _ = ∑ a, ∑ b, inv a b * koszul dg a b i := by
      simp only [lower_christoffel g inv dg hi]
    _ = loweredGaugeCovector inv dg i := by
      simp only [koszul, loweredGaugeCovector, metricContraction, ← mul_div_assoc,
        ← Finset.sum_div, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hswap]
      ring

private theorem twice_christoffel_expansion (inv : Tensor2) (dg : FirstJet) (a i j : Index) :
    2 * christoffel inv dg a i j =
      ∑ b, inv a b * (dg i j b + dg j i b - dg b i j) := by
  simp only [christoffel, koszul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Terms in coordinate Ricci that are linear in the second metric jet. -/
def principalRicci (inv : Tensor2) (d2g : SecondMetricJet) (i j : Index) : ℝ :=
  ∑ a, (christoffel inv (d2g a) a i j - christoffel inv (d2g j) a i a)

/-- The genuine second-derivative terms split into a scalar principal term
and the two derivatives of the lowered gauge covector. -/
theorem twice_principalRicci_eq_wave_and_gauge
    (inv : Tensor2) (d2g : SecondMetricJet) (hInv : IsSymmetricTensor inv)
    (hD : ∀ a b, d2g a b = d2g b a)
    (hG : ∀ a b, IsSymmetricTensor (d2g a b)) (i j : Index) :
    2 * principalRicci inv d2g i j =
      -(∑ a, ∑ b, inv a b * d2g a b i j) +
        loweredGaugeCovector inv (d2g i) j + loweredGaugeCovector inv (d2g j) i := by
  have hswap : (∑ a, ∑ b, inv a b * d2g j b i a) = ∑ a, ∑ b, inv a b * d2g j a i b :=
    metricContraction_swap inv hInv (fun a b => d2g j a i b)
  have hleft : (∑ a, ∑ b, inv a b * d2g i a b j) = ∑ a, ∑ b, inv a b * d2g i a j b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hG i a b j]
  have hright : (∑ a, ∑ b, inv a b * d2g j a b i) = ∑ a, ∑ b, inv a b * d2g j a i b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hG j a b i]
  calc
    2 * principalRicci inv d2g i j =
        ∑ a, ∑ b, inv a b * (d2g i a j b + d2g j b i a - d2g a b i j - d2g j i a b) := by
      unfold principalRicci
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_sub, twice_christoffel_expansion, twice_christoffel_expansion, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [hD a i, hD a j]
      ring
    _ = _ := by
      simp only [loweredGaugeCovector, metricContraction, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hswap, hleft, hright, hD i j]
      ring

end Burnett.P01
