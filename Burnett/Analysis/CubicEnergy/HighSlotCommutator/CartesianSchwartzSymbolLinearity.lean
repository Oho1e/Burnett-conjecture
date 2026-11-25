import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadianLimit
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.RadianHighDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.A07 (integrable_radianHighPairWeight_of_orderOne)
open Finset MeasureTheory
open scoped BigOperators

private theorem cartesianSchwartzPair_sum_symbols {ι : Type*} (I : Finset ι)
    (b : ι → Joint → ℂ) (B : ι → ℝ)
    (hMeas : ∀ i ∈ I, Measurable (b i))
    (hB0 : ∀ i ∈ I, 0≤B i)
    (hB : ∀ i ∈ I, ∀ z : Joint, ‖b i z‖≤B i*(1+‖z.1‖+‖z.2‖))
    (f g h : SchwartzMap E ℂ) :
    radianHighPair (fun z => ∑ i ∈ I, b i z) f g h =
      ∑ i ∈ I, radianHighPair (b i) f g h := by
  have hI (i : ι) (hi : i∈I) : Integrable (radianHighPairWeight (b i) f g h) :=
    integrable_radianHighPairWeight_of_orderOne (b i) (hMeas i hi) (B i) (hB0 i hi) (hB i hi) f g h
  have eq : radianHighPairWeight (fun z => ∑ i ∈ I, b i z) f g h =
      fun z => ∑ i ∈ I, radianHighPairWeight (b i) f g h z := by
    funext z
    simp only [radianHighPairWeight,sum_mul]
  simp only [radianHighPair,eq,integral_finset_sum I hI,smul_sum]

/-- The actual real-coefficient radian commutator is additive in a finite
sum of order-one symbols, using the original Schwartz inputs throughout. -/
theorem radianHighCommutatorPair_sum_schwartz_symbols {ι : Type*} (I : Finset ι)
    (b : ι → Joint → ℂ) (B : ι → ℝ)
    (hMeas : ∀ i ∈ I, Measurable (b i))
    (hB0 : ∀ i ∈ I, 0≤B i)
    (hB : ∀ i ∈ I, ∀ z : Joint, ‖b i z‖≤B i*(1+‖z.1‖+‖z.2‖))
    (D f g h : SchwartzMap E ℂ) :
    radianHighCommutatorPair (fun z => ∑ i ∈ I, b i z) (fun x => (D x).re) f g h =
      ∑ i ∈ I, radianHighCommutatorPair (b i) (fun x => (D x).re) f g h := by
  have eq (v : SchwartzMap E ℂ) :
      (fun x : E => ((D x).re : ℂ)*v x) = (gapSchwartzProduct (coefficientRealPart D) v : E → ℂ) :=
    funext fun x => by rw [gapSchwartzProduct_apply,coefficientRealPart_apply]
  simp only [radianHighCommutatorPair,eq,cartesianSchwartzPair_sum_symbols I b B hMeas hB0 hB,
    sum_sub_distrib]

/-- The two real-coefficient commutator terms add across the high and the
compact transition symbols on the same actual pairing. -/
theorem radianHighCommutatorPair_add_schwartz_symbols
    (b c : Joint → ℂ) (B C : ℝ) (hb : Measurable b) (hc : Measurable c)
    (hB0 : 0≤B) (hC0 : 0≤C)
    (hB : ∀ z : Joint, ‖b z‖≤B*(1+‖z.1‖+‖z.2‖))
    (hC : ∀ z : Joint, ‖c z‖≤C*(1+‖z.1‖+‖z.2‖))
    (D f g h : SchwartzMap E ℂ) :
    radianHighCommutatorPair (fun z => b z+c z) (fun x => (D x).re) f g h =
      radianHighCommutatorPair b (fun x => (D x).re) f g h +
        radianHighCommutatorPair c (fun x => (D x).re) f g h := by
  let F (v : Bool) := if v then b else c
  let M (v : Bool) := if v then B else C
  have hF (v : Bool) : Measurable (F v) := by cases v <;> assumption
  have hM (v : Bool) : 0≤M v := by cases v <;> assumption
  have hBound (v : Bool) (z : Joint) : ‖F v z‖ ≤ M v*(1+‖z.1‖+‖z.2‖) := by
    cases v
    · exact hC z
    · exact hB z
  simpa only [Fintype.sum_bool,F,Bool.false_eq_true,if_false,if_true] using
    radianHighCommutatorPair_sum_schwartz_symbols (Finset.univ : Finset Bool) F M
      (fun v _ => hF v) (fun v _ => hM v) (fun v _ => hBound v) D f g h

end Burnett.A06
