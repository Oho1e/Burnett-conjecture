import Burnett.Geometry.ConnectionDifference

/-!
# Exact coordinate Ricci difference

The Ricci array is computed from a connection and its first derivatives.
The covariant derivative of the connection difference is computed as that
of a tensor with one upper and two lower indices. No weak limit is used.
-/

noncomputable section

namespace Burnett.Geometry.CurvatureDifference

open scoped BigOperators
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference

abbrev ConnectionJet := Index → Connection

def covariantDerivative (Γ C : Connection) (dC : ConnectionJet)
    (d a b c : Index) : ℝ :=
  dC d a b c + ∑ e,
    (Γ a d e * C e b c - Γ e d b * C a e c - Γ e d c * C a b e)

def ricci (Γ : Connection) (dΓ : ConnectionJet) (b c : Index) : ℝ :=
  ∑ a, (dΓ a a b c - dΓ c a b a +
    ∑ e, (Γ a a e * Γ e b c - Γ a c e * Γ e b a))

def covariantDivergenceDifference (Γ C : Connection) (dC : ConnectionJet)
    (b c : Index) : ℝ :=
  ∑ a, (covariantDerivative Γ C dC a a b c -
    covariantDerivative Γ C dC c a b a)

def quadraticDifference (C : Connection) (b c : Index) : ℝ :=
  ∑ a, ∑ e, (C a a e * C e b c - C a c e * C e b a)

theorem covariant_contraction (Γ C : Connection) (dC : ConnectionJet)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hC : ∀ a b c, C a b c = C a c b) (a b c : Index) :
    covariantDerivative Γ C dC a a b c - covariantDerivative Γ C dC c a b a =
      dC a a b c - dC c a b a + ∑ e,
        (Γ a a e * C e b c + C a a e * Γ e b c -
          Γ a c e * C e b a - C a c e * Γ e b a) := by
  have hs :
      (∑ e, (Γ a a e * C e b c - Γ e a b * C a e c - Γ e a c * C a b e)) -
        (∑ e, (Γ a c e * C e b a - Γ e c b * C a e a - Γ e c a * C a b e)) =
      ∑ e, (Γ a a e * C e b c + C a a e * Γ e b c -
        Γ a c e * C e b a - C a c e * Γ e b a) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    rw [hΓ e a b, hΓ e c b, hΓ e c a, hC a e c, hC a e a]
    ring
  unfold covariantDerivative
  linarith [hs]

theorem ricci_add (Γ C : Connection) (dΓ dC : ConnectionJet)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hC : ∀ a b c, C a b c = C a c b) (b c : Index) :
    ricci (Γ + C) (dΓ + dC) b c - ricci Γ dΓ b c =
      covariantDivergenceDifference Γ C dC b c + quadraticDifference C b c := by
  unfold ricci covariantDivergenceDifference quadraticDifference
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [covariant_contraction Γ C dC hΓ hC]
  simp only [Pi.add_apply]
  have hs :
      (∑ e, ((Γ a a e + C a a e) * (Γ e b c + C e b c) -
        (Γ a c e + C a c e) * (Γ e b a + C e b a))) -
        (∑ e, (Γ a a e * Γ e b c - Γ a c e * Γ e b a)) =
      (∑ e, (Γ a a e * C e b c + C a a e * Γ e b c -
        Γ a c e * C e b a - C a c e * Γ e b a)) +
        ∑ e, (C a a e * C e b c - C a c e * C e b a) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  linarith [hs]

theorem ricci_difference (Γ₀ Γ₁ : Connection) (dΓ₀ dΓ₁ : ConnectionJet)
    (hΓ₀ : ∀ a b c, Γ₀ a b c = Γ₀ a c b)
    (hΓ₁ : ∀ a b c, Γ₁ a b c = Γ₁ a c b) (b c : Index) :
    ricci Γ₁ dΓ₁ b c - ricci Γ₀ dΓ₀ b c =
      covariantDivergenceDifference Γ₀ (Γ₁ - Γ₀) (dΓ₁ - dΓ₀) b c +
        quadraticDifference (Γ₁ - Γ₀) b c := by
  have hC : ∀ a b c, (Γ₁ - Γ₀) a b c = (Γ₁ - Γ₀) a c b := by
    intro a b c
    simp only [Pi.sub_apply, hΓ₁ a b c, hΓ₀ a b c]
  simpa only [add_sub_cancel] using
    ricci_add Γ₀ (Γ₁ - Γ₀) dΓ₀ (dΓ₁ - dΓ₀) hΓ₀ hC b c

/-! Actual coordinate derivatives of connection fields. -/

def coordinateConnectionJet (Γ : CoordinateSpace → Connection)
    (x : CoordinateSpace) : ConnectionJet :=
  fun d a b c => fderiv ℝ (fun y => Γ y a b c) x (EuclideanSpace.single d 1)

def DifferentiableConnectionAt (Γ : CoordinateSpace → Connection)
    (x : CoordinateSpace) : Prop :=
  ∀ a b c, DifferentiableAt ℝ (fun y => Γ y a b c) x

def coordinateRicci (Γ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (b c : Index) : ℝ := ricci (Γ x) (coordinateConnectionJet Γ x) b c

theorem coordinateConnectionJet_sub (Γ₁ Γ₀ : CoordinateSpace → Connection)
    (x : CoordinateSpace) (hd₁ : DifferentiableConnectionAt Γ₁ x)
    (hd₀ : DifferentiableConnectionAt Γ₀ x) :
    coordinateConnectionJet (fun y => Γ₁ y - Γ₀ y) x =
      coordinateConnectionJet Γ₁ x - coordinateConnectionJet Γ₀ x := by
  funext d a b c
  simp only [coordinateConnectionJet, Pi.sub_apply]
  rw [fderiv_fun_sub (hd₁ a b c) (hd₀ a b c), ContinuousLinearMap.sub_apply]

/-- The exact Ricci difference uses the actual derivative of Γ₁−Γ₀.
Torsion freedom and differentiability are required only at x. -/
theorem coordinateRicci_difference (Γ₀ Γ₁ : CoordinateSpace → Connection)
    (x : CoordinateSpace)
    (hΓ₀ : ∀ a b c, Γ₀ x a b c = Γ₀ x a c b)
    (hΓ₁ : ∀ a b c, Γ₁ x a b c = Γ₁ x a c b)
    (hd₀ : DifferentiableConnectionAt Γ₀ x)
    (hd₁ : DifferentiableConnectionAt Γ₁ x) (b c : Index) :
    coordinateRicci Γ₁ x b c - coordinateRicci Γ₀ x b c =
      covariantDivergenceDifference (Γ₀ x) (Γ₁ x - Γ₀ x)
        (coordinateConnectionJet (fun y => Γ₁ y - Γ₀ y) x) b c +
      quadraticDifference (Γ₁ x - Γ₀ x) b c := by
  rw [coordinateConnectionJet_sub Γ₁ Γ₀ x hd₁ hd₀]
  exact ricci_difference (Γ₀ x) (Γ₁ x) _ _ hΓ₀ hΓ₁ b c

/-- Applying the exact formula to a Ricci-flat second connection retains
both covariant derivative terms and the complete quadratic difference. -/
theorem coordinateRicci_vacuum_identity (Γ₀ Γ₁ : CoordinateSpace → Connection)
    (x : CoordinateSpace)
    (hΓ₀ : ∀ a b c, Γ₀ x a b c = Γ₀ x a c b)
    (hΓ₁ : ∀ a b c, Γ₁ x a b c = Γ₁ x a c b)
    (hd₀ : DifferentiableConnectionAt Γ₀ x)
    (hd₁ : DifferentiableConnectionAt Γ₁ x)
    (hVac : ∀ b c, coordinateRicci Γ₁ x b c = 0) (b c : Index) :
    0 = coordinateRicci Γ₀ x b c +
      covariantDivergenceDifference (Γ₀ x) (Γ₁ x - Γ₀ x)
        (coordinateConnectionJet (fun y => Γ₁ y - Γ₀ y) x) b c +
      quadraticDifference (Γ₁ x - Γ₀ x) b c := by
  have h := coordinateRicci_difference Γ₀ Γ₁ x hΓ₀ hΓ₁ hd₀ hd₁ b c
  rw [hVac b c] at h
  linarith

end Burnett.Geometry.CurvatureDifference
