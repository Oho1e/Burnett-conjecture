import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensityExtension
import Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol

set_option autoImplicit false
set_option maxHeartbeats 7600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate FourierTransform ContDiff

/-- The compact weight on the two sides of the existing cutoff sandwich. -/
def fixedChartInversePlateau (q : Space → ℝ) (hq : ContDiff ℝ ∞ (fun x => (q x)⁻¹))
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ)) : SchwartzMap Space ℂ :=
  (show HasCompactSupport (fun x => ψ x * ((q x)⁻¹ : ℝ)) from hψ.mul_right).toSchwartzMap
    ((ψ.smooth ⊤).mul (Complex.ofRealCLM.contDiff.comp hq))

@[simp] theorem fixedChartInversePlateau_apply (q : Space → ℝ) (hq : ContDiff ℝ ∞ (fun x => (q x)⁻¹))
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ)) (x : Space) :
    fixedChartInversePlateau q hq ψ hψ x = ψ x * ((q x : ℂ)⁻¹) := by
  change ψ x * (((q x)⁻¹ : ℝ) : ℂ) = _
  rw [Complex.ofReal_inv]

def fixedChartDensityConjugateSymbol (a : Space → Space → ℂ) (q : Space → ℝ)
    (χ : SchwartzMap Space ℂ) (x ξ : Space) : ℂ :=
  (q x : ℂ)^2 * cutoffSandwichSymbol a χ x ξ

theorem firstOrderAction_leftFactor (a : Space → Space → ℂ) (v : Space → ℂ)
    (f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction (fun y ξ => v y * a y ξ) f x = v x * firstOrderAction a f x := by
  simp only [firstOrderAction, Real.fourierIntegralInv_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  ring

/-- The exact square-root conjugation of the same localized Fourier action. -/
theorem firstOrderAction_fixedChartDensityConjugateSymbol {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (q : Space → ℝ) (hq : ContDiff ℝ ∞ (fun x => (q x)⁻¹))
    (hpos : ∀ x, 0 < q x) (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (f : SchwartzMap Space ℂ) (x : Space) :
    let χ := fixedChartInversePlateau q hq ψ hψ
    firstOrderAction (fixedChartDensityConjugateSymbol a q χ) f x =
      ((q x : ℂ) * ψ x) * firstOrderAction a (scalarSchwartzProduct χ f) x := by
  intro χ
  change firstOrderAction (fun y ξ => (q y : ℂ)^2 * cutoffSandwichSymbol a χ y ξ) f x = _
  rw [firstOrderAction_leftFactor, firstOrderAction_cutoffSandwichSymbol ha]
  change (q x : ℂ)^2 * (fixedChartInversePlateau q hq ψ hψ x *
    firstOrderAction a (scalarSchwartzProduct χ f) x) = _
  rw [fixedChartInversePlateau_apply]
  field_simp [Complex.ofReal_ne_zero.mpr (hpos x).ne']

theorem matrixFirstOrderAction_fixedChartDensityConjugateSymbol {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ (fun x => (q x)⁻¹)) (hpos : ∀ x, 0 < q x)
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    let χ := fixedChartInversePlateau q hq ψ hψ
    matrixFirstOrderAction (fun j k => fixedChartDensityConjugateSymbol (a j k) q χ) f i x =
      ((q x : ℂ)*ψ x) * matrixFirstOrderAction a (fun k => scalarSchwartzProduct χ (f k)) i x := by
  intro χ
  unfold matrixFirstOrderAction
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ =>
    firstOrderAction_fixedChartDensityConjugateSymbol (ha i j) q hq hpos ψ hψ (f j) x

/-- Formal symmetry for the original weighted action on compact fields in the chart. -/
def ChartDensityMatrixFormalSymmetry {ι : Type*} [Fintype ι]
    (W : Set Space) (ρ : Space → ℝ) (a : ι → ι → Space → Space → ℂ) : Prop :=
  ∀ f g : ι → SchwartzMap Space ℂ,
    (∀ i, HasCompactSupport (f i : Space → ℂ)) →
    (∀ i, HasCompactSupport (g i : Space → ℂ)) →
    (∀ i, tsupport (f i : Space → ℂ) ⊆ W) →
    (∀ i, tsupport (g i : Space → ℂ) ⊆ W) →
    (∑ i, ∫ x, (ρ x : ℂ) * (conj (g i x) * matrixFirstOrderAction a f i x)) =
      ∑ i, ∫ x, (ρ x : ℂ) * (conj (matrixFirstOrderAction a g i x) * f i x)

/-- The square-root conjugate is Lebesgue symmetric using only the original
weighted symmetry on compact supports inside the fixed chart. -/
theorem fixedChartDensityConjugateSymbol_formalSymmetry {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    {W : Set Space} {ρ : Space → ℝ} (hSym : ChartDensityMatrixFormalSymmetry W ρ a)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ (fun x => (q x)⁻¹)) (hpos : ∀ x, 0 < q x)
    (heq : EqOn (fun x => (q x)^2) ρ W) (ψ : SchwartzMap Space ℂ)
    (hψ : HasCompactSupport (ψ : Space → ℂ)) (hψs : tsupport (ψ : Space → ℂ) ⊆ W)
    (hψr : ∀ x, conj (ψ x) = ψ x) :
    MatrixFirstOrderFormalSymmetry (fun i j =>
      fixedChartDensityConjugateSymbol (a i j) q (fixedChartInversePlateau q hq ψ hψ)) := by
  intro f g
  let χ := fixedChartInversePlateau q hq ψ hψ
  let F := fun i => scalarSchwartzProduct χ (f i)
  let G := fun i => scalarSchwartzProduct χ (g i)
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport (ψ : Space → ℂ) := by
    apply closure_mono
    intro x hx
    have hx' : χ x ≠ 0 := hx
    intro h0
    exact hx' (by simp [χ, h0])
  have hSub (u : SchwartzMap Space ℂ) :
      tsupport (scalarSchwartzProduct χ u : Space → ℂ) ⊆ tsupport (ψ : Space → ℂ) := by
    apply Set.Subset.trans _ hχs
    apply closure_mono
    intro x hx
    have hx' : scalarSchwartzProduct χ u x ≠ 0 := hx
    intro h0
    exact hx' (by simp [scalarSchwartzProduct_apply, h0])
  have hC (u : SchwartzMap Space ℂ) : HasCompactSupport (scalarSchwartzProduct χ u : Space → ℂ) :=
    hψ.of_isClosed_subset isClosed_closure (hSub u)
  have hWeight (x : Space) : (ρ x : ℂ) * χ x = (q x : ℂ)*ψ x := by
    by_cases h : x ∈ W
    · have hr : (ρ x : ℂ) = (q x : ℂ)^2 := by exact_mod_cast (heq h).symm
      rw [hr]
      simp only [χ, fixedChartInversePlateau_apply]
      field_simp [Complex.ofReal_ne_zero.mpr (hpos x).ne']
    · have hz : ψ x = 0 := by
        by_contra hne
        exact h (hψs (subset_closure hne))
      simp [χ, hz]
  have hχr (x : Space) : conj (χ x) = χ x := by
    simp [χ, map_mul, hψr]
  have hqr (x : Space) : conj ((q x : ℂ)*ψ x) = (q x : ℂ)*ψ x := by
    simp [map_mul, hψr]
  have h := hSym F G (fun i => hC (f i)) (fun i => hC (g i))
    (fun i => (hSub (f i)).trans hψs) (fun i => (hSub (g i)).trans hψs)
  simp only [matrixFirstOrderAction_fixedChartDensityConjugateSymbol ha q hq hpos ψ hψ]
  calc
    _ = ∑ i, ∫ x, (ρ x : ℂ) * (conj (G i x) * matrixFirstOrderAction a F i x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      simp only [G, scalarSchwartzProduct_apply, map_mul, hχr]
      rw [← hWeight x]
      ring
    _ = ∑ i, ∫ x, (ρ x : ℂ) * (conj (matrixFirstOrderAction a G i x) * F i x) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      simp only [F, scalarSchwartzProduct_apply, map_mul, hqr]
      rw [← hWeight x]
      ring

end Burnett.Analysis.CarlesonEmbedding
