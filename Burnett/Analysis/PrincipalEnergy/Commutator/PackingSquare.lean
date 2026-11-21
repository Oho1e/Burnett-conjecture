import Burnett.Analysis.PrincipalEnergy.Commutator.PackingLevels
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Classical

private theorem square_distribution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ) (hF : Measurable F) (hN : ∀ x, 0 ≤ F x) :
    (∫⁻ x, ENNReal.ofReal ((F x)^2) ∂μ) =
      ∫⁻ t in Ioi (0:ℝ), μ {x | t < F x} * ENNReal.ofReal (2*t) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (g := fun t : ℝ => 2*t) μ
    (Eventually.of_forall hN) hF.aemeasurable
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
        exact mul_nonneg (by norm_num) (le_of_lt ht))
  have hPrimitive (s : ℝ) : (∫ t in (0:ℝ)..s, 2*t) = s^2 := by
    rw [intervalIntegral.integral_const_mul,integral_id]
    ring
  simpa only [hPrimitive] using h

/-- Finite Carleson embedding for nested-or-disjoint sets. The spatial
majorant belongs to the actual underlying measure space. -/
theorem finite_packing_square_le {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (Q : ι → Set X)
    (mQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hinj : ∀ i ∈ I, ∀ j ∈ I, Q i = Q j → i = j)
    (nested : ∀ i ∈ I, ∀ j ∈ I, Q i ⊆ Q j ∨ Q j ⊆ Q i ∨ Disjoint (Q i) (Q j))
    (w : ι → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (pack : ∀ j ∈ I, (∑ i ∈ I.filter (fun i => Q i ⊆ Q j), w i) ≤ C*μ (Q j))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : X → ℝ) (hF : Measurable F) (hN : ∀ x, 0 ≤ F x)
    (dom : ∀ i ∈ I, ∀ x ∈ Q i, a i ≤ F x) :
    (∑ i ∈ I, w i*ENNReal.ofReal ((a i)^2)) ≤ C*∫⁻ x, ENNReal.ofReal ((F x)^2) ∂μ := by
  classical
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hA : Measurable a := fun _ _ => MeasurableSpace.measurableSet_top
  let ν : Measure ι := ∑ i ∈ I, w i • Measure.dirac i
  have hMass (t : ℝ) : ν {i | t < a i} = ∑ i ∈ I.filter (fun i => t < a i), w i := by
    dsimp only [ν]
    rw [Measure.finset_sum_apply,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t < a i
    · simp [hi,Measure.smul_apply]
    · simp [hi,Measure.smul_apply]
  have hIntegral : (∫⁻ i, ENNReal.ofReal ((a i)^2) ∂ν) =
      ∑ i ∈ I, w i*ENNReal.ofReal ((a i)^2) := by
    dsimp only [ν]
    simp only [lintegral_finset_sum_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  rw [← hIntegral,square_distribution ν a hA ha,square_distribution μ F hF hN]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), (C*μ {x | t < F x})*ENNReal.ofReal (2*t) := by
      apply lintegral_mono
      intro t
      apply mul_le_mul_right'
      rw [hMass]
      exact finite_packing_level_le μ I Q mQ hinj nested w C pack a F dom t
    _ = _ := by
      simp only [mul_assoc]
      exact lintegral_const_mul' _ _ hC

end Burnett.Analysis.CarlesonEmbedding
