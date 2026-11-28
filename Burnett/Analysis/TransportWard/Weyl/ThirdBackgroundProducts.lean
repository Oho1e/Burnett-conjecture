import Burnett.Analysis.TransportWard.Weyl.ThirdVariationA03Bridge
import Burnett.Analysis.TransportWard.Weyl.DirectionCoefficientJets

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4100

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

def eulerThirdVariationCoefficientOrderTwo {J : Type*} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (s t : ActionSlot J) (i j : J) (x : E) : ℝ :=
  secondFDeriv (metricActionCoefficient S s t) (assembleMetricComponents S (g x)) (S i) (S j)

def eulerThirdVariationCoefficientOrderThree {J : Type*} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (s t : ActionSlot J) (i j l : J) (x : E) : ℝ :=
  secondFDeriv (fderiv ℝ (metricActionCoefficient S s t))
    (assembleMetricComponents S (g x)) (S i) (S j) (S l)

/-- The three background terms are explicitly scalar products. Only the
first differentiates the test, and that term has two undifferentiated
perturbations. -/
theorem coordinateActionThirdVariationDensity_eq_A03_principal_add_componentProducts
    {J : Type} [Fintype J] (S : J → Mat) (g : E → J → ℝ) (z w : RealEnergyField J)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U)
    (hG : (assembleMetricComponents S (g x)).det ≠ 0) :
    let h (y : E) (i : J) := (z.val i y).re
    let k (y : E) (i : J) := (w.val i y).re
    let p := coordinateMetricFirstJet g x
    let q := coordinateMetricFirstJet h x
    let v := coordinateMetricFirstJet k x
    let C₂ (s t : ActionSlot J) (i j : J) := eulerThirdVariationCoefficientOrderTwo S g s t i j x
    let C₃ (s t : ActionSlot J) (i j l : J) := eulerThirdVariationCoefficientOrderThree S g s t i j l x
    coordinateActionThirdVariationDensity S g h k x =
      (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x).re +
      (∑ s, ∑ t, ∑ i, ∑ j, C₂ s t i j * p t * h x i * h x j * v s) +
      (∑ s, ∑ t, ∑ i, ∑ j, C₂ s t i j * h x i * k x j * (q s * p t + p s * q t)) +
      (∑ s, ∑ t, ∑ i, ∑ j, ∑ l, (1 / 2 : ℝ) * C₃ s t i j l * p s * p t * h x i * h x j * k x l) := by
  intro h k p q v C₂ C₃
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  let K := assembleMetricComponents S (k x)
  let C (s t : ActionSlot J) := metricActionCoefficient S s t
  let CK (s t : ActionSlot J) (A : Mat) := fderiv ℝ (C s t) A K
  have hExact := coordinateActionThirdVariationDensity_eq_A03_principal_add_background S g z w hU hg x hx hG
  dsimp only at hExact
  rw [hExact]
  have h₂HH (s t : ActionSlot J) :
      secondFDeriv (C s t) G H H = ∑ i, ∑ j, (h x i * h x j) * C₂ s t i j :=
    assembledMetricDirections_twoSlots S (h x) (h x) (secondFDeriv (C s t) G)
  have h₂HK (s t : ActionSlot J) :
      fderiv ℝ (CK s t) G H = ∑ i, ∑ j, (h x i * k x j) * C₂ s t i j := by
    rw [(directionalCoefficient_fderiv_and_secondFDeriv (C s t) isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S s t) hG K).1 H]
    exact assembledMetricDirections_twoSlots S (h x) (k x) (secondFDeriv (C s t) G)
  have h₃HHK (s t : ActionSlot J) :
      secondFDeriv (CK s t) G H H = ∑ i, ∑ j, ∑ l, (h x i * h x j * k x l) * C₃ s t i j l := by
    rw [(directionalCoefficient_fderiv_and_secondFDeriv (C s t) isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S s t) hG K).2 H H]
    exact assembledMetricDirections_threeSlots S (h x) (h x) (k x)
      (secondFDeriv (fderiv ℝ (C s t)) G)
  let F₀ (s t : ActionSlot J) := secondFDeriv (C s t) G H H * v s * p t
  let F₁ (s t : ActionSlot J) := fderiv ℝ (CK s t) G H * (q s * p t + p s * q t)
  let F₂ (s t : ActionSlot J) := (1 / 2 : ℝ) * secondFDeriv (CK s t) G H H * p s * p t
  change _ + (∑ s, ∑ t, (F₀ s t + F₁ s t + F₂ s t)) = _
  have he₀ (s t : ActionSlot J) :
      F₀ s t = ∑ i, ∑ j, C₂ s t i j * p t * h x i * h x j * v s := by
    dsimp only [F₀]
    rw [h₂HH]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he₁ (s t : ActionSlot J) :
      F₁ s t = ∑ i, ∑ j, C₂ s t i j * h x i * k x j * (q s * p t + p s * q t) := by
    dsimp only [F₁]
    rw [h₂HK]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he₂ (s t : ActionSlot J) :
      F₂ s t = ∑ i, ∑ j, ∑ l, (1 / 2 : ℝ) * C₃ s t i j l * p s * p t * h x i * h x j * k x l := by
    dsimp only [F₂]
    rw [h₃HHK]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [Finset.sum_add_distrib, he₀, he₁, he₂, add_assoc]

end Burnett.V03.Palatini
