import Burnett.Analysis.TransportWard.Weyl.EulerQuadraticJet

set_option autoImplicit false
set_option maxHeartbeats 3700000

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.C02
open Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

open private orderedTensorBasis from Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients

local notation "E₀" => CoordinateSpace

theorem assembleMetricComponents_orderedBasis (h : OrderedPair → ℝ) :
    assembleMetricComponents frozenActionOrderedBasis h = fun a b => h (a,b) := by
  classical
  ext a b
  rw [assembleMetricComponents_apply, Matrix.sum_apply]
  have hδ (i j : Index) : Matrix.single i j (1 : ℝ) a b =
      if i = a then (if j = b then 1 else 0) else 0 := by
    by_cases hi : i = a <;> by_cases hj : j = b <;> simp [Matrix.single, hi, hj]
  simp only [frozenActionOrderedBasis, orderedTensorBasis, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, hδ]
  simp [mul_ite]

/-- The principal quadratic Euler field on the frozen background is negative
twice the two original A02 cubic arrays. The derivative is real. -/
theorem frozenEuler_secondAffineDerivative_eq_completeCubicFields
    (G : Mat) (hG : G ∈ nonsingularMetricDomain) {U : Set E₀} (hU : IsOpen U)
    (h : E₀ → OrderedPair → ℝ) (hh : ContDiffOn ℝ ∞ h U) (x : E₀) (hx : x ∈ U) (k : OrderedPair) :
    let g (_ : E₀) (i : OrderedPair) := G i.1 i.2
    let d := coordinateMetricFirstJet h x
    let e := coordinateMetricSecondJet h x
    deriv (deriv (fun t : ℝ => coordinateDensityEuler frozenActionOrderedBasis
      (fun y => g y + t • h y) x k)) 0 =
      -2 * ((∑ a : Index, ∑ s : ActionSlot OrderedPair,
        (∑ j : OrderedPair, frozenActionCubicLinear G ((a,s.1),(k,s.2)) j * h x j) * e a s) +
        ∑ s : ActionSlot OrderedPair, ∑ t : ActionSlot OrderedPair,
          frozenActionCubicQuadratic G s.1 t.1 s.2 t.2 k * d s * d t) := by
  intro g d e
  have ha : assembleMetricComponents frozenActionOrderedBasis (g x) = G := by
    rw [assembleMetricComponents_orderedBasis]
  have hg₁ (y : E₀) (s : ActionSlot OrderedPair) : coordinateMetricFirstJet g y s = 0 := by
    change fderiv ℝ (fun _ : E₀ => (fun j : OrderedPair => G j.1 j.2)) y (coordinateBasis s.1) s.2 = 0
    simp
  have hg₂ (a : Index) (s : ActionSlot OrderedPair) : coordinateMetricSecondJet g x a s = 0 := by
    simp only [coordinateMetricSecondJet, hg₁, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  have hc (a : Index) (s : ActionSlot OrderedPair) :
      fderiv ℝ (metricActionCoefficient frozenActionOrderedBasis (a,k) s) G
        (assembleMetricComponents frozenActionOrderedBasis (h x)) =
      ∑ j : OrderedPair, frozenActionCubicLinear G ((a,s.1),(k,s.2)) j * h x j := by
    rw [assembleMetricComponents_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul]
    rw [← frozenActionCubicLinear_eq_metricActionCoefficient_fderiv G hG a s.1 k s.2 j]
    exact mul_comm _ _
  have hnd : (assembleMetricComponents frozenActionOrderedBasis (g x)).det ≠ 0 := by
    simpa only [ha] using hG
  have hLow (s t : ActionSlot OrderedPair) : metricEulerLowerCoefficient frozenActionOrderedBasis k s t G =
      -frozenActionCubicQuadratic G s.1 t.1 s.2 t.2 k := by
    rcases s with ⟨a,i⟩
    rcases t with ⟨d,j⟩
    exact metricEulerLowerCoefficient_ordered_eq_neg_frozenActionCubicQuadratic G hG a d i j k
  have hJ := coordinateDensityEuler_secondAffineDerivative_eq_jets frozenActionOrderedBasis hU g h
    (show ContDiffOn ℝ ∞ g U from contDiffOn_const) hh x hx k hnd
  dsimp only at hJ
  rw [hJ]
  simp only [ha, hg₁, hg₂, mul_zero, zero_mul, add_zero, zero_add, hc, hLow]
  have hA (s t : ActionSlot OrderedPair) :
      (2 : ℝ) * -frozenActionCubicQuadratic G s.1 t.1 s.2 t.2 k * d s * d t =
        (-2 : ℝ) * (frozenActionCubicQuadratic G s.1 t.1 s.2 t.2 k * d s * d t) := by ring
  have hB (a : Index) (s : ActionSlot OrderedPair) :
      (2 : ℝ) * (∑ j : OrderedPair, frozenActionCubicLinear G ((a,s.1),(k,s.2)) j * h x j) * e a s =
        (2 : ℝ) * ((∑ j : OrderedPair, frozenActionCubicLinear G ((a,s.1),(k,s.2)) j * h x j) * e a s) := by ring
  change (∑ s : ActionSlot OrderedPair, ∑ t : ActionSlot OrderedPair,
      (2 : ℝ) * -frozenActionCubicQuadratic G s.1 t.1 s.2 t.2 k * d s * d t) -
      (∑ a : Index, ∑ s : ActionSlot OrderedPair,
        (2 : ℝ) * (∑ j : OrderedPair, frozenActionCubicLinear G ((a,s.1),(k,s.2)) j * h x j) * e a s) = _
  simp only [hA, hB]
  simp only [← Finset.mul_sum]
  ring

end Burnett.V03.Palatini
