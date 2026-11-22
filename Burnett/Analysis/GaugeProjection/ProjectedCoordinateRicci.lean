import Burnett.Analysis.GaugeProjection.ProjectedRicciPrincipal
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators

/-- The actual second coordinate derivatives of the pulled-back metric. -/
def coordinateSecondMetricJet (g : CoordinateSpace → Tensor2) (x : CoordinateSpace) : SecondMetricJet :=
  fun k i a b => fderiv ℝ (fun y => coordinateJet g y i a b) x (EuclideanSpace.single k 1)

private theorem hasFDerivAt_koszul_coordinateJet (g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x) (i j q : Index) :
    HasFDerivAt (fun y => koszul (coordinateJet g y) i j q)
      ((1 / 2 : ℝ) • (fderiv ℝ (fun y => coordinateJet g y i j q) x +
        fderiv ℝ (fun y => coordinateJet g y j i q) x -
        fderiv ℝ (fun y => coordinateJet g y q i j) x)) x := by
  have h := (((hD i j q).hasFDerivAt.add (hD j i q).hasFDerivAt).sub
    (hD q i j).hasFDerivAt).const_smul (1 / 2 : ℝ)
  have eq : (fun y => koszul (coordinateJet g y) i j q) =
      (fun y => (1 / 2 : ℝ) •
        (coordinateJet g y i j q + coordinateJet g y j i q - coordinateJet g y q i j)) := by
    funext y
    simp only [koszul, smul_eq_mul]
    ring
  rw [eq]
  exact h

/-- Differentiating the actual computed Christoffel symbols uses the product
rule for the inverse metric and the first metric jet. -/
theorem coordinateConnectionJet_computed_product
    (inv g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hInv : DifferentiableComponentsAt inv x)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x) :
    coordinateConnectionJet (fun y => christoffel (inv y) (coordinateJet g y)) x =
      fun k a b c => christoffel (coordinateJet inv x k) (coordinateJet g x) a b c +
        christoffel (inv x) (coordinateSecondMetricJet g x k) a b c := by
  funext k a b c
  have hK (j : Index) := hasFDerivAt_koszul_coordinateJet g x hD b c j
  have hTerm : ∀ j ∈ Finset.univ, DifferentiableAt ℝ
      (fun y => inv y a j * koszul (coordinateJet g y) b c j) x :=
    fun j _ => (hInv a j).mul (hK j).differentiableAt
  simp only [coordinateConnectionJet, christoffel]
  rw [fderiv_fun_sum hTerm, ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (hInv a j) (hK j).differentiableAt, (hK j).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    coordinateJet, coordinateSecondMetricJet, koszul, smul_eq_mul]
  ring

/-- The terms in coordinate Ricci that use only the metric and inverse first
jets. -/
def firstJetRicciRemainder (inv : Tensor2) (dg dinv : FirstJet) (i j : Index) : ℝ :=
  ricci (christoffel inv dg) (fun k => christoffel (dinv k) dg) i j

theorem coordinateRicci_eq_principal_add_firstJet
    (inv g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hInv : DifferentiableComponentsAt inv x)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x)
    (i j : Index) :
    coordinateRicci (fun y => christoffel (inv y) (coordinateJet g y)) x i j =
      principalRicci (inv x) (coordinateSecondMetricJet g x) i j +
      firstJetRicciRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j := by
  unfold coordinateRicci firstJetRicciRemainder principalRicci
  rw [coordinateConnectionJet_computed_product inv g x hInv hD]
  simp only [ricci, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The scalar wave term and the principal derivative of the lowered gauge
covector in the actual coordinate Ricci operator. -/
theorem twice_coordinateRicci_eq_wave_gauge_and_firstJet
    (inv g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hInv : DifferentiableComponentsAt inv x)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x)
    (hSym : IsSymmetricTensor (inv x))
    (hMixed : ∀ a b, coordinateSecondMetricJet g x a b = coordinateSecondMetricJet g x b a)
    (hMetric : ∀ a b, IsSymmetricTensor (coordinateSecondMetricJet g x a b))
    (i j : Index) :
    2 * coordinateRicci (fun y => christoffel (inv y) (coordinateJet g y)) x i j =
      -(∑ a, ∑ b, inv x a b * coordinateSecondMetricJet g x a b i j) +
        loweredGaugeCovector (inv x) (coordinateSecondMetricJet g x i) j +
        loweredGaugeCovector (inv x) (coordinateSecondMetricJet g x j) i +
        2 * firstJetRicciRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j := by
  rw [coordinateRicci_eq_principal_add_firstJet inv g x hInv hD, mul_add,
    twice_principalRicci_eq_wave_and_gauge (inv x) (coordinateSecondMetricJet g x) hSym hMixed hMetric]

end Burnett.P01
