import Burnett.Geometry.CurvatureDifference

/-! The exact connection and curvature constructions use the same ordered
index contractions as F06. The quadratic Ricci correction is minus B. -/

noncomputable section

namespace Burnett.Geometry.CurvatureSymbolBridge

open scoped BigOperators
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference

theorem christoffel_rankOneJet (G : Tensor2) (ξ : Covector) (k : Tensor2)
    (a b c : Index) :
    christoffel G (fun d i j => ξ d * k i j) a b c =
      connectionSymbol G ξ k a b c := by
  unfold christoffel koszul connectionSymbol raiseSecond raiseCovector
  calc
    (∑ d, G a d * ((ξ b * k c d + ξ c * k b d - ξ d * k b c) / 2)) =
        ∑ d, (ξ b * (G a d * k c d) + ξ c * (G a d * k b d) -
          (G a d * ξ d) * k b c) / 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]

theorem quadraticDifference_connectionSymbol (G : Tensor2) (ξ : Covector)
    (k : Tensor2) (b c : Index) :
    quadraticDifference (connectionSymbol G ξ k) b c = -quadraticSymbol G ξ k b c := by
  unfold quadraticDifference quadraticSymbol
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem quadraticDifference_rankOneJet (G : Tensor2) (ξ : Covector)
    (k : Tensor2) (b c : Index) :
    quadraticDifference (christoffel G (fun d i j => ξ d * k i j)) b c =
      -quadraticSymbol G ξ k b c := by
  have heq : christoffel G (fun d i j => ξ d * k i j) = connectionSymbol G ξ k := by
    funext a i j
    exact christoffel_rankOneJet G ξ k a i j
  rw [heq]
  exact quadraticDifference_connectionSymbol G ξ k b c

end Burnett.Geometry.CurvatureSymbolBridge
