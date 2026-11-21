import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensityPairing

set_option autoImplicit false
set_option maxHeartbeats 8500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff

/-- The left cutoff for the weighted pairing written in Lebesgue measure. -/
def fixedChartWeightedLeftPlateau (q : Space → ℝ) (hq : ContDiff ℝ ∞ q)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ)) : SchwartzMap Space ℂ :=
  (show HasCompactSupport (fun x => (q x : ℂ)^2 * ψ x) from hψ.mul_left).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp hq).pow 2).mul (ψ.smooth ⊤))

@[simp] theorem fixedChartWeightedLeftPlateau_apply (q : Space → ℝ) (hq : ContDiff ℝ ∞ q)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ)) (x : Space) :
    fixedChartWeightedLeftPlateau q hq ψ hψ x = (q x : ℂ)^2*ψ x := rfl

theorem fixedChartWeightedLeftPlateau_compact (q : Space → ℝ) (hq : ContDiff ℝ ∞ q)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ)) :
    HasCompactSupport (fixedChartWeightedLeftPlateau q hq ψ hψ : Space → ℂ) := hψ.mul_left

theorem matrixFirstOrderAction_fixedChartWeightedLocalSymbol {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j)) (q : Space → ℝ)
    (hq : ContDiff ℝ ∞ q) (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    matrixFirstOrderAction (fun j k => fixedChartDensityConjugateSymbol (a j k) q ψ) f i x =
      (fixedChartWeightedLeftPlateau q hq ψ hψ) x *
        matrixFirstOrderAction a (fun k => scalarSchwartzProduct ψ (f k)) i x := by
  rw [fixedChartWeightedLeftPlateau_apply]
  unfold matrixFirstOrderAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change firstOrderAction (fun y ξ => (q y : ℂ)^2 * cutoffSandwichSymbol (a i j) ψ y ξ) (f j) x = _
  rw [firstOrderAction_leftFactor, firstOrderAction_cutoffSandwichSymbol (ha i j), mul_assoc]

/-- The exact weight of the original pairing gives a Lebesgue symmetric
localized symbol with a root factor on each side of the unitary conjugate. -/
theorem fixedChartWeightedLocalSymbol_formalSymmetry {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    {W : Set Space} {ρ : Space → ℝ} (hSym : ChartDensityMatrixFormalSymmetry W ρ a)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q) (heq : EqOn (fun x => (q x)^2) ρ W)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (hψs : tsupport (ψ : Space → ℂ) ⊆ W) (hψr : ∀ x, conj (ψ x) = ψ x) :
    MatrixFirstOrderFormalSymmetry (fun i j => fixedChartDensityConjugateSymbol (a i j) q ψ) := by
  intro f g
  let F := fun i => scalarSchwartzProduct ψ (f i)
  let G := fun i => scalarSchwartzProduct ψ (g i)
  have hSub (u : SchwartzMap Space ℂ) :
      tsupport (scalarSchwartzProduct ψ u : Space → ℂ) ⊆ tsupport (ψ : Space → ℂ) := by
    apply closure_mono
    intro x hx
    change scalarSchwartzProduct ψ u x ≠ 0 at hx
    intro h0
    exact hx (by simp [scalarSchwartzProduct_apply, h0])
  have hC (u : SchwartzMap Space ℂ) : HasCompactSupport (scalarSchwartzProduct ψ u : Space → ℂ) :=
    hψ.of_isClosed_subset isClosed_closure (hSub u)
  have hP (x : Space) : (fixedChartWeightedLeftPlateau q hq ψ hψ) x = (ρ x : ℂ)*ψ x := by
    rw [fixedChartWeightedLeftPlateau_apply]
    by_cases h : x ∈ W
    · have hc : (q x : ℂ)^2 = (ρ x : ℂ) := by exact_mod_cast heq h
      rw [hc]
    · have h0 : ψ x = 0 := by
        by_contra hn
        exact h (hψs (subset_closure hn))
      rw [h0, mul_zero, mul_zero]
  have h := hSym F G (fun i => hC (f i)) (fun i => hC (g i))
    (fun i => (hSub (f i)).trans hψs) (fun i => (hSub (g i)).trans hψs)
  simp only [matrixFirstOrderAction_fixedChartWeightedLocalSymbol ha q hq ψ hψ, hP]
  calc
    _ = ∑ i, ∫ x, (ρ x : ℂ) * (conj (G i x) * matrixFirstOrderAction a F i x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      simp only [G, scalarSchwartzProduct_apply, map_mul, hψr]
      ring
    _ = ∑ i, ∫ x, (ρ x : ℂ) * (conj (matrixFirstOrderAction a G i x) * F i x) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      simp only [F, scalarSchwartzProduct_apply, map_mul, Complex.conj_ofReal, hψr]
      ring

end Burnett.Analysis.CarlesonEmbedding
