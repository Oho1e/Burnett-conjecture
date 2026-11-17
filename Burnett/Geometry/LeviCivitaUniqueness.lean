import Burnett.Geometry.BackgroundConnection

/-!
# Uniqueness of the torsion-free metric connection coefficients

This is a pointwise uniqueness theorem, including the actual inverse supplied
by a nondegenerate metric. It does not construct a global connection or assume
that coordinate first derivatives transform as a tensor.
-/

noncomputable section

namespace Burnett.Geometry.LeviCivitaUniqueness

open scoped BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

theorem lower_of_torsion_free_metric_compatible
    (g : Tensor2) (dg : FirstJet) (Γ : Connection)
    (hg : IsSymmetricTensor g) (ht : ∀ e b c, Γ e b c = Γ e c b)
    (hm : ∀ b c d, covariantJet Γ g dg b c d = 0) (b c d : Index) :
    (∑ e, Γ e b c * g e d) = koszul dg b c d := by
  have hz : covariantJet Γ g dg = 0 := by
    funext b c d
    exact hm b c d
  have hk := koszul_covariantJet Γ g dg ht hg b c d
  rw [hz] at hk
  have hzero : koszul (0 : FirstJet) b c d = 0 := by simp [koszul]
  rw [hzero] at hk
  exact (sub_eq_zero.mp hk.symm).symm

theorem eq_christoffel_of_torsion_free_metric_compatible
    (g gInv : Tensor2) (dg : FirstJet) (Γ : Connection)
    (hg : IsSymmetricTensor g)
    (hi : ∀ a e, (∑ d, gInv a d * g d e) = if a = e then 1 else 0)
    (ht : ∀ e b c, Γ e b c = Γ e c b)
    (hm : ∀ b c d, covariantJet Γ g dg b c d = 0) :
    Γ = christoffel gInv dg := by
  funext a b c
  have hl (d : Index) : (∑ e, g d e * Γ e b c) = koszul dg b c d := by
    simpa only [hg d, mul_comm] using
      lower_of_torsion_free_metric_compatible g dg Γ hg ht hm b c d
  calc
    Γ a b c = ∑ d, gInv a d * (∑ e, g d e * Γ e b c) :=
      (inverse_contract g gInv hi (fun e => Γ e b c) a).symm
    _ = christoffel gInv dg a b c := by simp only [hl, christoffel]

theorem metricConnection_unique
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn : (g x).Nondegenerate) (hs : (g x).IsSymm)
    (Γ : Connection) (ht : ∀ e b c, Γ e b c = Γ e c b)
    (hm : ∀ b c d, covariantJet Γ (metricComponents g x)
      (coordinateJet (metricComponents g) x) b c d = 0) :
    Γ = metricConnection g x hn := by
  exact eq_christoffel_of_torsion_free_metric_compatible _ _ _ Γ
    (FiberMetric.covariant_symmetric _ hs coordinateBasis)
    (FiberMetric.contravariant_mul_covariant _ hn hs coordinateBasis) ht hm

theorem computedConnection_unique
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn : (g x).Nondegenerate) (hs : (g x).IsSymm)
    (Γ : Connection) (ht : ∀ e b c, Γ e b c = Γ e c b)
    (hm : ∀ b c d, covariantJet Γ (metricComponents g x)
      (coordinateJet (metricComponents g) x) b c d = 0) :
    Γ = BackgroundConnection.computedConnection g x := by
  rw [BackgroundConnection.computedConnection_eq_metricConnection g x hn hs]
  exact metricConnection_unique g x hn hs Γ ht hm

end Burnett.Geometry.LeviCivitaUniqueness
