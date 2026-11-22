import Burnett.Analysis.GaugeProjection.ProjectedCoordinateRicci

set_option autoImplicit false
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators

private theorem loweredGaugeCovector_sum (inv : Tensor2) (dg : FirstJet) (j : Index) :
    loweredGaugeCovector inv dg j =
      ∑ a, ∑ b, inv a b * (dg a b j - dg j a b / 2) := by
  change (∑ a, ∑ b, inv a b * dg a b j) - (∑ a, ∑ b, inv a b * dg j a b) / 2 = _
  simp only [mul_sub, ← mul_div_assoc, ← Finset.sum_div, Finset.sum_sub_distrib]

/-- The lowered contracted Christoffel vector as an actual coordinate field. -/
def coordinateGaugeCovector (inv g : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) (j : Index) : ℝ :=
  loweredGaugeCovector (inv x) (coordinateJet g x) j

private def gaugeJetEntry (dg : FirstJet) (a b j : Index) : ℝ :=
  dg a b j - dg j a b / 2

private theorem gaugeJetEntry_hasFDerivAt (g : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x)
    (a b j : Index) :
    HasFDerivAt (fun y => gaugeJetEntry (coordinateJet g y) a b j)
      (fderiv ℝ (fun y => coordinateJet g y a b j) x -
        (1 / 2 : ℝ) • fderiv ℝ (fun y => coordinateJet g y j a b) x) x := by
  have h := (hD a b j).hasFDerivAt.sub ((hD j a b).hasFDerivAt.const_smul (1 / 2 : ℝ))
  have he : (fun y => gaugeJetEntry (coordinateJet g y) a b j) =
      fun y => coordinateJet g y a b j - (1 / 2 : ℝ) • coordinateJet g y j a b := by
    funext y
    simp only [gaugeJetEntry, smul_eq_mul]
    ring
  rw [he]
  exact h

/-- Differentiation of the actual lowered gauge covector. -/
theorem coordinateGaugeCovector_coordinateDerivative
    (inv g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hInv : DifferentiableComponentsAt inv x)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x)
    (i j : Index) :
    fderiv ℝ (fun y => coordinateGaugeCovector inv g y j) x (EuclideanSpace.single i 1) =
      loweredGaugeCovector (coordinateJet inv x i) (coordinateJet g x) j +
      loweredGaugeCovector (inv x) (coordinateSecondMetricJet g x i) j := by
  have hEq : (fun y => coordinateGaugeCovector inv g y j) =
      fun y => ∑ a, ∑ b, inv y a b * gaugeJetEntry (coordinateJet g y) a b j := by
    funext y
    exact loweredGaugeCovector_sum (inv y) (coordinateJet g y) j
  have hK (a b : Index) := gaugeJetEntry_hasFDerivAt g x hD a b j
  have hF (a : Index) : ∀ b ∈ Finset.univ, DifferentiableAt ℝ
      (fun y => inv y a b * gaugeJetEntry (coordinateJet g y) a b j) x :=
    fun b _ => (hInv a b).mul (hK a b).differentiableAt
  have hSum : ∀ a ∈ Finset.univ, DifferentiableAt ℝ
      (fun y => ∑ b, inv y a b * gaugeJetEntry (coordinateJet g y) a b j) x :=
    fun a _ => (HasFDerivAt.fun_sum fun b hb => (hF a b hb).hasFDerivAt).differentiableAt
  rw [hEq, fderiv_fun_sum hSum, ContinuousLinearMap.sum_apply,
    loweredGaugeCovector_sum, loweredGaugeCovector_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_sum (hF a), ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [fderiv_fun_mul (hInv a b) (hK a b).differentiableAt, (hK a b).fderiv]
  simp only [coordinateJet, coordinateSecondMetricJet, gaugeJetEntry,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- The part of twice Ricci left after taking the scalar wave term and the
full symmetrized gauge derivative. Every metric jet in it is first order. -/
def projectedSourceFirstJetRemainder (inv : Tensor2) (dg dinv : FirstJet) (i j : Index) : ℝ :=
  2 * firstJetRicciRemainder inv dg dinv i j -
    loweredGaugeCovector (dinv i) dg j - loweredGaugeCovector (dinv j) dg i

/-- The no-gauge coordinate Ricci equation in the form needed before
applying the Fourier projection. -/
theorem twice_coordinateRicci_eq_wave_symmetrizedGauge_remainder
    (inv g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hInv : DifferentiableComponentsAt inv x)
    (hD : ∀ i a b, DifferentiableAt ℝ (fun y => coordinateJet g y i a b) x)
    (hSym : IsSymmetricTensor (inv x))
    (hMixed : ∀ a b, coordinateSecondMetricJet g x a b = coordinateSecondMetricJet g x b a)
    (hMetric : ∀ a b, IsSymmetricTensor (coordinateSecondMetricJet g x a b)) (i j : Index) :
    2 * coordinateRicci (fun y => christoffel (inv y) (coordinateJet g y)) x i j =
      -(∑ a, ∑ b, inv x a b * coordinateSecondMetricJet g x a b i j) +
        fderiv ℝ (fun y => coordinateGaugeCovector inv g y j) x (EuclideanSpace.single i 1) +
        fderiv ℝ (fun y => coordinateGaugeCovector inv g y i) x (EuclideanSpace.single j 1) +
        projectedSourceFirstJetRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j := by
  rw [twice_coordinateRicci_eq_wave_gauge_and_firstJet inv g x hInv hD hSym hMixed hMetric,
    coordinateGaugeCovector_coordinateDerivative inv g x hInv hD i j,
    coordinateGaugeCovector_coordinateDerivative inv g x hInv hD j i]
  unfold projectedSourceFirstJetRemainder
  ring

end Burnett.P01
