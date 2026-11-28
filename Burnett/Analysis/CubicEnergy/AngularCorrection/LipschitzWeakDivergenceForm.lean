import Burnett.Analysis.CubicEnergy.AngularCorrection.PaperAnalyticCorrectionBounds

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A08

open MeasureTheory Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped BigOperators ComplexConjugate ENNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

open private inner_left_schwartzDivergence inner_right_schwartzDivergence
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

/-- A bounded real coefficient as a physical-space multiplication symbol. -/
def boundedRealCoefficient (d : E → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hm : Measurable d) (hd : ∀ x, |d x| ≤ D) : BoundedSymbol E where
  toFun x := d x
  measurable := (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable
  bound := D
  bound_nonneg := hD
  norm_le x := by rw [Complex.norm_real]; exact hd x

theorem boundedRealCoefficient_schwartz_product (d : SchwartzMap E ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ x, |d x| ≤ D) (v : Test) :
    symbolCLM (boundedRealCoefficient d D hD d.continuous.measurable hd) (v.toLp 2 volume) =
      (realSchwartzMultiply d v).toLp 2 volume := by
  let c := boundedRealCoefficient d D hD d.continuous.measurable hd
  change symbolL2 c (v.toLp 2 volume) = _
  apply Lp.ext
  filter_upwards [symbolL2_ae c (v.toLp 2 volume), v.coeFn_toLp 2 volume,
    (realSchwartzMultiply d v).coeFn_toLp 2 volume] with x h₁ h₂ h₃
  change symbolL2 c (v.toLp 2 volume) x = (realSchwartzMultiply d v).toLp 2 volume x
  rw [h₁, h₂, h₃, realSchwartzMultiply_apply]
  rfl

namespace OriginalAnalyticCorrectionBounds

variable {b : Joint → ℂ} {C : ℝ}

/-- The genuine weak derivative of the forward correction output, in L². -/
def forwardCoordinateOutput (P : OriginalAnalyticCorrectionBounds b C)
    (a : Fin 4) (H u : Test) : LP2 :=
  P.forward H (coordinateDerivative a u) + P.forward (coordinateDerivative a H) u

/-- The genuine weak derivative of the high-adjoint correction output, in L². -/
def adjointCoordinateOutput (P : OriginalAnalyticCorrectionBounds b C)
    (a : Fin 4) (H u : Test) : LP2 :=
  P.adjoint H (coordinateDerivative a u) + P.adjoint (coordinateDerivative a H) u

theorem forwardCoordinateOutput_test (P : OriginalAnalyticCorrectionBounds b C)
    (a : Fin 4) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.forwardCoordinateOutput a H u) =
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P.forward H u) := by
  rw [forwardCoordinateOutput, inner_add_right, ← (P.coordinate_commutator a H u w).1]
  abel

theorem adjointCoordinateOutput_test (P : OriginalAnalyticCorrectionBounds b C)
    (a : Fin 4) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (P.adjointCoordinateOutput a H u) =
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P.adjoint H u) := by
  rw [adjointCoordinateOutput, inner_add_right, ← (P.coordinate_commutator a H u w).2]
  abel

end OriginalAnalyticCorrectionBounds

/-- The weak commutator of the divergence form with the actual correction.
For a real symmetric coefficient matrix, the first term places the divergence
on the test; the second uses the actual high adjoint. Every product is in L². -/
def boundedWeakDivergenceCommutatorPair {b : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds b C)
    (d : Fin 4 → Fin 4 → BoundedSymbol E) (H u w : Test) : ℂ :=
  (∑ a : Fin 4, ∑ j : Fin 4,
    inner ℂ (symbolCLM (d a j) ((coordinateDerivative a w).toLp 2 volume))
      (P.forwardCoordinateOutput j H u)) -
  ∑ a : Fin 4, ∑ j : Fin 4, inner ℂ (P.adjointCoordinateOutput a H w)
    (symbolCLM (d a j) ((coordinateDerivative j u).toLp 2 volume))

/-- The weak divergence definition specializes exactly to the original
Schwartz-coefficient divergence commutator. -/
theorem boundedWeakDivergenceCommutatorPair_eq_schwartz {b : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds b C)
    (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (hs : ∀ a j, d a j = d j a)
    (D : ℝ) (hD : 0 ≤ D) (hd : ∀ a j x, |d a j x| ≤ D) (H u w : Test) :
    boundedWeakDivergenceCommutatorPair P
      (fun a j => boundedRealCoefficient (d a j) D hD (d a j).continuous.measurable (hd a j)) H u w =
      weakDivergenceCommutatorPair d (P.forward H) u w := by
  unfold boundedWeakDivergenceCommutatorPair
  simp_rw [boundedRealCoefficient_schwartz_product]
  have right (a j : Fin 4) :
      inner ℂ (P.adjointCoordinateOutput a H w)
        ((realSchwartzMultiply (d a j) (coordinateDerivative j u)).toLp 2 volume) =
      -inner ℂ (P.adjoint H w)
        ((coordinateDerivative a (realSchwartzMultiply (d a j) (coordinateDerivative j u))).toLp 2 volume) := by
    have eq := congrArg (conj : ℂ → ℂ)
      (P.adjointCoordinateOutput_test a H w (realSchwartzMultiply (d a j) (coordinateDerivative j u)))
    simpa only [inner_conj_symm, map_neg] using eq
  simp_rw [P.forwardCoordinateOutput_test, right, Finset.sum_neg_distrib]
  rw [weakDivergenceCommutatorPair, P.adjoint_duality H (schwartzDivergence d u) w,
    inner_left_schwartzDivergence, inner_right_schwartzDivergence]
  congr 1
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => -z)
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => by rw [hs j a]))

end Burnett.A08
