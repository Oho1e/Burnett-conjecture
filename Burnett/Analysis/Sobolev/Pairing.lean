import Burnett.Analysis.Sobolev.TestJet
import Burnett.Analysis.Sobolev.GraphDual

/- Tree-external bridge from the genuine five-component Sobolev test jet to
Bochner integrals.  Equality of Lp representatives is used only almost
everywhere.  No distribution-space or weak-derivative identification is
asserted by this file. -/
noncomputable section

open MeasureTheory

namespace Burnett.X02.TestJetPairing

open SobolevTestJet

def coefficients (g : ScalarL2) (V : Fin 4 → ScalarL2) : JetSpace :=
  WithLp.toLp 2 (Fin.cases g (fun i => -V i))

@[simp] theorem coefficients_zero (g : ScalarL2) (V : Fin 4 → ScalarL2) :
    coefficients g V 0 = g := rfl

@[simp] theorem coefficients_succ (g : ScalarL2) (V : Fin 4 → ScalarL2) (i : Fin 4) :
    coefficients g V i.succ = -V i := rfl

theorem real_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  simp [mul_comm]

theorem valueLp_ae_eq (φ : D) :
    (valueLp φ : Space → ℝ) =ᵐ[volume] (φ : Space → ℝ) :=
  (test_memLp φ).coeFn_toLp

theorem directionalLp_ae_eq (i : Fin 4) (φ : D) :
    (directionalLp i φ : Space → ℝ) =ᵐ[volume]
      directional i (φ : Space → ℝ) :=
  (directional_memLp i φ).coeFn_toLp

theorem integrable_value_product (g : ScalarL2) (φ : D) :
    Integrable (fun x : Space => g x * (φ : Space → ℝ) x) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) g (valueLp φ)).congr
  filter_upwards [valueLp_ae_eq φ] with x hx
  rw [real_inner_eq_mul, hx]

theorem integrable_directional_product (V : ScalarL2) (i : Fin 4) (φ : D) :
    Integrable (fun x : Space => V x * directional i (φ : Space → ℝ) x) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) V (directionalLp i φ)).congr
  filter_upwards [directionalLp_ae_eq i φ] with x hx
  rw [real_inner_eq_mul, hx]

theorem inner_valueLp (g : ScalarL2) (φ : D) :
    inner ℝ g (valueLp φ) = ∫ x : Space, g x * (φ : Space → ℝ) x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [valueLp_ae_eq φ] with x hx
  rw [real_inner_eq_mul, hx]

theorem inner_directionalLp (V : ScalarL2) (i : Fin 4) (φ : D) :
    inner ℝ V (directionalLp i φ) =
      ∫ x : Space, V x * directional i (φ : Space → ℝ) x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [directionalLp_ae_eq i φ] with x hx
  rw [real_inner_eq_mul, hx]

/-- The coefficient functional evaluates on the actual test function and
its actual directional derivatives, rather than arbitrary Lp representatives. -/
theorem coefficientFunctional_test (g : ScalarL2) (V : Fin 4 → ScalarL2) (φ : D) :
    GraphDual.coefficientFunctional J (coefficients g V) (GraphDual.testMap J φ) =
      (∫ x : Space, g x * (φ : Space → ℝ) x) -
        ∑ i : Fin 4, ∫ x : Space, V i x * directional i (φ : Space → ℝ) x := by
  rw [GraphDual.coefficientFunctional_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  change inner ℝ g (valueLp φ) + ∑ i : Fin 4, inner ℝ (-V i) (directionalLp i φ) = _
  simp only [inner_neg_left, Finset.sum_neg_distrib, inner_valueLp, inner_directionalLp]
  rfl

theorem integrable_value_product_of_memLp (g : Space → ℝ)
    (hg : MemLp g 2 (volume : Measure Space)) (φ : D) :
    Integrable (fun x : Space => g x * (φ : Space → ℝ) x) volume := by
  apply (integrable_value_product (hg.toLp g) φ).congr
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem integrable_directional_product_of_memLp (V : Space → ℝ)
    (hV : MemLp V 2 (volume : Measure Space)) (i : Fin 4) (φ : D) :
    Integrable (fun x : Space => V x * directional i (φ : Space → ℝ) x) volume := by
  apply (integrable_directional_product (hV.toLp V) i φ).congr
  filter_upwards [hV.coeFn_toLp] with x hx
  rw [hx]

/-- Concrete L² coefficient functions can be used without identifying their
chosen Lp representatives pointwise with the original functions. -/
theorem coefficientFunctional_test_of_memLp (g : Space → ℝ) (V : Fin 4 → Space → ℝ)
    (hg : MemLp g 2 (volume : Measure Space))
    (hV : ∀ i, MemLp (V i) 2 (volume : Measure Space)) (φ : D) :
    GraphDual.coefficientFunctional J
        (coefficients (hg.toLp g) (fun i => (hV i).toLp (V i)))
        (GraphDual.testMap J φ) =
      (∫ x : Space, g x * (φ : Space → ℝ) x) -
        ∑ i : Fin 4, ∫ x : Space, V i x * directional i (φ : Space → ℝ) x := by
  rw [coefficientFunctional_test]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [(hV i).coeFn_toLp] with x hx
    rw [hx]

#print axioms integrable_value_product
#print axioms integrable_directional_product
#print axioms coefficientFunctional_test
#print axioms coefficientFunctional_test_of_memLp

end Burnett.X02.TestJetPairing
