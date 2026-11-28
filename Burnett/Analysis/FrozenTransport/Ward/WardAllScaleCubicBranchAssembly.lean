import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicCubicExpansion
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchAssembly

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 18200000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.RicciSymbol Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight comparableSlotWeight)
open Burnett.V08 (signedCyclicPhase)

private abbrev WardSlotSpectrum := E → ComplexTensor2

private def wardTriadFirstFixedSwap : Joint ≃ᵐ Joint where
  toFun x := (x.1, -(x.1+x.2))
  invFun x := (x.1, -(x.1+x.2))
  left_inv x := by
    apply Prod.ext
    · rfl
    · change -(x.1 + -(x.1+x.2)) = x.2
      abel
  right_inv x := by
    apply Prod.ext
    · rfl
    · change -(x.1 + -(x.1+x.2)) = x.2
      abel
  measurable_toFun := measurable_fst.prodMk (measurable_fst.add measurable_snd).neg
  measurable_invFun := measurable_fst.prodMk (measurable_fst.add measurable_snd).neg

private theorem wardTriadFirstFixedSwap_preserves :
    MeasurePreserving wardTriadFirstFixedSwap (volume : Measure Joint) volume := by
  have hSwap : MeasurePreserving (Prod.swap : Joint → Joint) (volume : Measure Joint) volume := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.measurePreserving_swap
  have h := measurePreserving_radianCycle.comp hSwap
  have hEq : (⇑radianCycle : Joint → Joint) ∘ Prod.swap = wardTriadFirstFixedSwap := by
    funext x
    change (x.1, -(x.2+x.1)) = (x.1, -(x.1+x.2))
    rw [add_comm x.2 x.1]
  exact hEq ▸ h

private theorem wardCyclicCubicWeight_fixedSwap (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) :
    wardCyclicCubicWeight G a F H J (wardTriadFirstFixedSwap x) = wardCyclicCubicWeight G a F J H x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hq : -(p+r) = q := by dsimp [r]; abel
  have hα : signedCyclicPhase a p r = signedCyclicPhase a p q := by
    unfold signedCyclicPhase
    rw [hq, add_comm (a p) (a r)]
    change a r + a p + a q = a p + a q + a r
    ring
  change (-Complex.I / 3) * (signedCyclicPhase a p r : ℂ) *
    complexPrincipalVertex G (fun d => p d) (F p) (fun d => r d) (H r) (fun d => (-(p+r)) d) (J (-(p+r))) =
    (-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
    complexPrincipalVertex G (fun d => p d) (F p) (fun d => q d) (J q) (fun d => r d) (H r)
  rw [hq, hα, complexPrincipalVertex_cyclic G (fun d => p d) (F p),
    complexPrincipalVertex_swap_first_two G (fun d => r d) (H r),
    ← complexPrincipalVertex_cyclic G (fun d => p d) (F p)]

private theorem wardLowSlotWeight_swap_high (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : E) :
    lowSlotWeight ϑ κ p q r = lowSlotWeight ϑ κ p r q := by
  unfold lowSlotWeight
  rw [add_comm (‖q‖ ^ 2) (‖r‖ ^ 2)]

/-- The original cubic energy with one of the four exact signed cutoff weights. -/
def wardCyclicCubicBranchWeight (ϑ : ℝ → ℝ) (κ : ℝ) (b : Fin 4)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) : ℂ :=
  (radianFourBranchWeight ϑ κ b x : ℂ) * wardCyclicCubicWeight G a F H J x

def wardCyclicCubicBranchForm (ϑ : ℝ → ℝ) (κ : ℝ) (b : Fin 4)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) : ℂ :=
  (tau ^ 8)⁻¹ • ∫ x, wardCyclicCubicBranchWeight ϑ κ b G a F H J x

theorem wardCyclicCubicBranchWeight_first_cycle (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) :
    wardCyclicCubicBranchWeight ϑ κ 0 G a F H J (radianCycle x) =
      wardCyclicCubicBranchWeight ϑ κ 1 G a J F H x := by
  unfold wardCyclicCubicBranchWeight
  rw [wardCyclicCubicWeight_cycle]
  congr 1
  have h : -((radianCycle x).1 + (radianCycle x).2) = x.1 := by
    change -(x.2 + -(x.1+x.2)) = x.1
    abel
  change (lowSlotWeight ϑ κ (radianCycle x).1 (radianCycle x).2
    (-((radianCycle x).1 + (radianCycle x).2)) : ℂ) =
      (lowSlotWeight ϑ κ (radianCycle x).1 (radianCycle x).2 x.1 : ℂ)
  rw [h]

theorem wardCyclicCubicBranchWeight_comparable_cycle (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) :
    wardCyclicCubicBranchWeight ϑ κ 3 G a F H J (radianCycle x) =
      wardCyclicCubicBranchWeight ϑ κ 3 G a J F H x := by
  unfold wardCyclicCubicBranchWeight
  rw [wardCyclicCubicWeight_cycle]
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hp : -(q+r) = p := by dsimp [r]; abel
  congr 1
  change (comparableSlotWeight ϑ κ q r (-(q+r)) : ℂ) = (comparableSlotWeight ϑ κ p q r : ℂ)
  rw [hp]
  push_cast [comparableSlotWeight]
  ring

theorem wardCyclicCubicBranchWeight_second_fixedSwap (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) :
    wardCyclicCubicBranchWeight ϑ κ 1 G a F H J (wardTriadFirstFixedSwap x) =
      wardCyclicCubicBranchWeight ϑ κ 2 G a F J H x := by
  unfold wardCyclicCubicBranchWeight
  rw [wardCyclicCubicWeight_fixedSwap]
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hq : -(p+r) = q := by dsimp [r]; abel
  congr 1
  change (lowSlotWeight ϑ κ r (-(p+r)) p : ℂ) = (lowSlotWeight ϑ κ r p q : ℂ)
  rw [hq, wardLowSlotWeight_swap_high ϑ κ r q p]

theorem wardCyclicCubicBranchForm_first_cycle (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) :
    wardCyclicCubicBranchForm ϑ κ 1 G a J F H = wardCyclicCubicBranchForm ϑ κ 0 G a F H J := by
  unfold wardCyclicCubicBranchForm
  rw [← measurePreserving_radianCycle.integral_comp' (wardCyclicCubicBranchWeight ϑ κ 0 G a F H J)]
  simp only [wardCyclicCubicBranchWeight_first_cycle]

theorem wardCyclicCubicBranchForm_comparable_cycle (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) :
    wardCyclicCubicBranchForm ϑ κ 3 G a J F H = wardCyclicCubicBranchForm ϑ κ 3 G a F H J := by
  unfold wardCyclicCubicBranchForm
  conv_rhs =>
    rw [← measurePreserving_radianCycle.integral_comp' (wardCyclicCubicBranchWeight ϑ κ 3 G a F H J)]
  simp only [wardCyclicCubicBranchWeight_comparable_cycle]

theorem wardCyclicCubicBranchForm_second_fixedSwap (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) :
    wardCyclicCubicBranchForm ϑ κ 2 G a F J H = wardCyclicCubicBranchForm ϑ κ 1 G a F H J := by
  unfold wardCyclicCubicBranchForm
  rw [← wardTriadFirstFixedSwap_preserves.integral_comp' (wardCyclicCubicBranchWeight ϑ κ 1 G a F H J)]
  simp only [wardCyclicCubicBranchWeight_second_fixedSwap]

/-- The exact four cutoffs recover the original polarized cyclic energy. -/
theorem wardCyclicCubicForm_sum_branches (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum)
    (hInt : ∀ b, Integrable (wardCyclicCubicBranchWeight ϑ κ b G a F H J)) :
    wardCyclicCubicForm G a F H J = ∑ b, wardCyclicCubicBranchForm ϑ κ b G a F H J := by
  have hPoint : (fun x => ∑ b, wardCyclicCubicBranchWeight ϑ κ b G a F H J x) =
      wardCyclicCubicWeight G a F H J := funext
    (radianFourBranchSymbol_sum ϑ κ (wardCyclicCubicWeight G a F H J))
  unfold wardCyclicCubicForm wardCyclicCubicBranchForm
  rw [← hPoint, integral_finset_sum Finset.univ (fun b _ => hInt b), Finset.smul_sum]


private theorem wardCyclicCubicBranchWeight_first_fixedSwap (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) (x : Joint) :
    wardCyclicCubicBranchWeight ϑ κ 0 G a F H J (wardTriadFirstFixedSwap x) =
      wardCyclicCubicBranchWeight ϑ κ 0 G a F J H x := by
  unfold wardCyclicCubicBranchWeight
  rw [wardCyclicCubicWeight_fixedSwap]
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hq : -(p+r) = q := by dsimp [r]; abel
  congr 1
  change (lowSlotWeight ϑ κ p r (-(p+r)) : ℂ) = (lowSlotWeight ϑ κ p q r : ℂ)
  rw [hq, wardLowSlotWeight_swap_high ϑ κ p r q]

private theorem wardCyclicCubicBranchForm_first_fixedSwap (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum) :
    wardCyclicCubicBranchForm ϑ κ 0 G a F J H = wardCyclicCubicBranchForm ϑ κ 0 G a F H J := by
  unfold wardCyclicCubicBranchForm
  conv_rhs =>
    rw [← wardTriadFirstFixedSwap_preserves.integral_comp' (wardCyclicCubicBranchWeight ϑ κ 0 G a F H J)]
  simp only [wardCyclicCubicBranchWeight_first_fixedSwap]

private theorem wardCyclicCubicWeight_integrable_of_branches (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (F H J : WardSlotSpectrum)
    (h : ∀ b, Integrable (wardCyclicCubicBranchWeight ϑ κ b G a F H J)) :
    Integrable (wardCyclicCubicWeight G a F H J) :=
  (integrable_finset_sum Finset.univ (fun j _ => h j)).congr
    (Filter.Eventually.of_forall (radianFourBranchSymbol_sum ϑ κ (wardCyclicCubicWeight G a F H J)))
/-- For one gauge leg the two physical-low sectors share one integral;
the comparable sector is in the same physical, physical, gauge ordering. -/
theorem wardCyclicCubicForm_oneGauge_sectorSum (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (P Q : WardSlotSpectrum)
    (h₀ : Integrable (wardCyclicCubicBranchWeight ϑ κ 0 G a Q P P))
    (h₁ : Integrable (wardCyclicCubicBranchWeight ϑ κ 0 G a P P Q))
    (h₃ : Integrable (wardCyclicCubicBranchWeight ϑ κ 3 G a P P Q)) :
    Integrable (wardCyclicCubicWeight G a Q P P) ∧
    wardCyclicCubicForm G a Q P P =
      wardCyclicCubicBranchForm ϑ κ 0 G a Q P P + 2 * wardCyclicCubicBranchForm ϑ κ 0 G a P P Q +
        wardCyclicCubicBranchForm ϑ κ 3 G a P P Q := by
  let W := wardCyclicCubicBranchWeight ϑ κ
  have hFirst : Integrable (W 1 G a Q P P) :=
    (measurePreserving_radianCycle.integrable_comp_of_integrable h₁).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_first_cycle ϑ κ G a P P Q))
  have hSecond : Integrable (W 2 G a Q P P) :=
    (wardTriadFirstFixedSwap_preserves.integrable_comp_of_integrable hFirst).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_second_fixedSwap ϑ κ G a Q P P))
  have hComp : Integrable (W 3 G a Q P P) :=
    (measurePreserving_radianCycle.integrable_comp_of_integrable h₃).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_comparable_cycle ϑ κ G a P P Q))
  have hInt (b : Fin 4) : Integrable (W b G a Q P P) := by
    fin_cases b
    · exact h₀
    · exact hFirst
    · exact hSecond
    · exact hComp
  refine ⟨wardCyclicCubicWeight_integrable_of_branches ϑ κ G a Q P P hInt,?_⟩
  rw [wardCyclicCubicForm_sum_branches ϑ κ G a Q P P hInt, Fin.sum_univ_four,
    wardCyclicCubicBranchForm_second_fixedSwap ϑ κ G a Q P P,
    wardCyclicCubicBranchForm_first_cycle ϑ κ G a P P Q,
    wardCyclicCubicBranchForm_comparable_cycle ϑ κ G a P P Q]
  ring

/-- For two gauge legs both gauge-low sectors use the genuine
gauge, physical, gauge ordering with the first frequency low. -/
theorem wardCyclicCubicForm_twoGauge_sectorSum (ϑ : ℝ → ℝ) (κ : ℝ)
    (G : Mat) (a : E → ℝ) (P Q : WardSlotSpectrum)
    (h₀ : Integrable (wardCyclicCubicBranchWeight ϑ κ 0 G a P Q Q))
    (h₁ : Integrable (wardCyclicCubicBranchWeight ϑ κ 0 G a Q P Q))
    (h₃ : Integrable (wardCyclicCubicBranchWeight ϑ κ 3 G a P Q Q)) :
    Integrable (wardCyclicCubicWeight G a P Q Q) ∧
    wardCyclicCubicForm G a P Q Q =
      wardCyclicCubicBranchForm ϑ κ 0 G a P Q Q + 2 * wardCyclicCubicBranchForm ϑ κ 0 G a Q P Q +
        wardCyclicCubicBranchForm ϑ κ 3 G a P Q Q := by
  let W := wardCyclicCubicBranchWeight ϑ κ
  have hRotate : Integrable (W 0 G a Q Q P) :=
    (wardTriadFirstFixedSwap_preserves.integrable_comp_of_integrable h₁).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_first_fixedSwap ϑ κ G a Q P Q))
  have hFirst : Integrable (W 1 G a P Q Q) :=
    (measurePreserving_radianCycle.integrable_comp_of_integrable hRotate).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_first_cycle ϑ κ G a Q Q P))
  have hSecond : Integrable (W 2 G a P Q Q) :=
    (wardTriadFirstFixedSwap_preserves.integrable_comp_of_integrable hFirst).congr
      (Filter.Eventually.of_forall (wardCyclicCubicBranchWeight_second_fixedSwap ϑ κ G a P Q Q))
  have hInt (b : Fin 4) : Integrable (W b G a P Q Q) := by
    fin_cases b
    · exact h₀
    · exact hFirst
    · exact hSecond
    · exact h₃
  refine ⟨wardCyclicCubicWeight_integrable_of_branches ϑ κ G a P Q Q hInt,?_⟩
  rw [wardCyclicCubicForm_sum_branches ϑ κ G a P Q Q hInt, Fin.sum_univ_four,
    wardCyclicCubicBranchForm_second_fixedSwap ϑ κ G a P Q Q,
    wardCyclicCubicBranchForm_first_cycle ϑ κ G a Q Q P,
    wardCyclicCubicBranchForm_first_fixedSwap ϑ κ G a Q P Q]
  ring

end Burnett.C02
