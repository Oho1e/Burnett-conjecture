import Burnett.Analysis.PrincipalEnergy.Quantization.HormanderOrderOne
import Burnett.Analysis.PrincipalEnergy
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.A02.FrequencySplit (radianFourier radianFourier_scaled tau)
open scoped BigOperators ComplexConjugate ContDiff ENNReal FourierTransform RealInnerProductSpace

theorem globalMatrixSymbolData_of_hormanderOrderOne {ι : Type*} {a : ι → ι → Space → Space → ℂ}
    (ha : ∀ i j, HormanderOrderOne (a i j))
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j))) :
    GlobalMatrixSymbolData a where
  frequency i j := (ha i j).firstBaseFrequencyOrderOne
  smooth i j := (ha i j).smooth
  pureBase i j := (ha i j).pureBase
  proper := hProper

theorem globalMatrixDerivativeSymbolData_of_hormanderOrderOne {ι : Type*}
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, HormanderOrderOne (a i j)) :
    GlobalMatrixDerivativeSymbolData a where
  frequency i j b := ((ha i j).baseDirection (coordinateDirection b)).firstBaseFrequencyOrderOne
  pureBase i j b := ((ha i j).baseDirection (coordinateDirection b)).pureBase

/-- The supremum of the component `L∞` seminorms in the fixed chart. -/
def componentEssentialBound {κ V : Type*} [SeminormedAddCommGroup V] (v : κ → Space → V) : ℝ≥0∞ :=
  ⨆ k, eLpNormEssSup (v k) volume

/-- For smooth coefficients, the value and the classical first derivative
have finite `L∞` seminorms exactly when the coordinate `W¹,∞` norm is finite. -/
def HasFiniteCoordinateW1Infty {κ : Type*} (r : κ → Space → ℂ) : Prop :=
  componentEssentialBound r < ⊤ ∧ componentEssentialBound (fun k => fderiv ℝ (r k)) < ⊤

/-- A coordinate `W¹,∞` norm using the largest component bounds. -/
def coordinateW1Infty {κ : Type*} (r : κ → Space → ℂ) : ℝ :=
  (componentEssentialBound r).toReal + (componentEssentialBound (fun k => fderiv ℝ (r k))).toReal

private theorem ae_component_bound {κ V : Type*} [SeminormedAddCommGroup V] (v : κ → Space → V)
    (hv : componentEssentialBound v < ⊤) (k : κ) :
    ∀ᵐ x ∂(volume : Measure Space), ‖v k x‖ ≤ (componentEssentialBound v).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := v k) (μ := volume)] with x hx
  simpa using ENNReal.toReal_mono hv.ne (hx.trans (le_iSup (fun j => eLpNormEssSup (v j) volume) k))

/-- `lem:commutator`, real symmetric scalar coefficients and a fixed
properly supported, formally symmetric matrix first-order operator. -/
theorem originalScalarLipschitzEnergy {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, HormanderOrderOne (a i j))
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j)))
    (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → Space → ℂ),
      (∀ b d, ContDiff ℝ ∞ (r b d)) →
      (∀ b d x, conj (r b d x) = r b d x) →
      (∀ b d x, r b d x = r d b x) →
      let entries : Fin 4 × Fin 4 → Space → ℂ := fun i => r i.1 i.2
      HasFiniteCoordinateW1Infty entries → ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (matrixFirstOrderAction a f.val i x) *
          compactScalarPrincipalField r f i x).im| ≤ C * coordinateW1Infty entries *
            (compactMatrixCoordinateH1 f)^2 := by
  obtain ⟨C, hC, hBound⟩ := exists_actual_scalarCoefficient_principal_energy_bound
    (globalMatrixSymbolData_of_hormanderOrderOne ha hProper)
    (globalMatrixDerivativeSymbolData_of_hormanderOrderOne ha) hSym
  refine ⟨C, hC, ?_⟩
  intro r hr hReal hSymmetric entries hFinite f
  let U := (componentEssentialBound entries).toReal
  let L := (componentEssentialBound (fun k => fderiv ℝ (entries k))).toNNReal
  apply hBound r hr L U ENNReal.toReal_nonneg hReal hSymmetric
  · intro b d
    exact ae_component_bound entries hFinite.1 (b, d)
  · intro b d
    exact ae_component_bound (fun k => fderiv ℝ (entries k)) hFinite.2 (b, d)

/-- `lem:commutator`, Hermitian matrix coefficients and a fixed operator
whose full symbol is scalar on the field components. -/
theorem originalHermitianLipschitzEnergy {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : HormanderOrderOne a) (hProper : ProperKernelRelation (firstOrderKernelRelation a))
    (hSym : FirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ),
      (∀ b d i j, ContDiff ℝ ∞ (r b d i j)) →
      (∀ b d i j x, conj (r b d i j x) = r d b j i x) →
      let entries : Fin 4 × Fin 4 × ι × ι → Space → ℂ := fun i => r i.1 i.2.1 i.2.2.1 i.2.2.2
      HasFiniteCoordinateW1Infty entries → ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (firstOrderAction a (f.val i) x) *
          compactFinitePrincipalField r f i x).im| ≤ C * coordinateW1Infty entries *
            (compactMatrixCoordinateH1 f)^2 := by
  obtain ⟨C, hC, hBound⟩ := exists_actual_matrixCoefficient_principal_energy_bound (ι := ι)
    ha.firstBaseFrequencyOrderOne ha.smooth ha.pureBase
    (fun b => (ha.baseDirection (coordinateDirection b)).firstBaseFrequencyOrderOne)
    (fun b => (ha.baseDirection (coordinateDirection b)).pureBase) hProper hSym
  refine ⟨C, hC, ?_⟩
  intro r hr hHermitian entries hFinite f
  let U := (componentEssentialBound entries).toReal
  let L := (componentEssentialBound (fun k => fderiv ℝ (entries k))).toNNReal
  apply hBound r hr L U ENNReal.toReal_nonneg hHermitian
  · intro b d i j
    exact ae_component_bound entries hFinite.1 (b, d, i, j)
  · intro b d i j
    exact ae_component_bound (fun k => fderiv ℝ (entries k)) hFinite.2 (b, d, i, j)

/-- The same full symbol in mathlib's frequency convention. -/
def cycleFrequencySymbol (a : Space → Space → ℂ) (x ν : Space) : ℂ := a x (tau • ν)

/-- Left quantization in the manuscript's radian frequencies, including the
four-dimensional inverse Fourier factor. -/
def radianFirstOrderAction (a : Space → Space → ℂ) (f : Space → ℂ) (x : Space) : ℂ :=
  (tau ^ 4)⁻¹ • ∫ ζ, Complex.exp ((inner ℝ ζ x : ℂ) * Complex.I) * (a x ζ * radianFourier f ζ)

theorem radianFirstOrderAction_eq (a : Space → Space → ℂ) (f : Space → ℂ) (x : Space) :
    radianFirstOrderAction a f x = firstOrderAction (cycleFrequencySymbol a) f x := by
  let F (ζ : Space) := Complex.exp ((inner ℝ ζ x : ℂ) * Complex.I) * (a x ζ * radianFourier f ζ)
  have hTau : 0 ≤ tau := by unfold tau; positivity
  have hChange := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) F tau (hR := hTau)
  rw [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin] at hChange
  unfold radianFirstOrderAction firstOrderAction
  rw [← hChange, Real.fourierIntegralInv_eq']
  apply integral_congr_ae
  filter_upwards with ν
  simp only [F, real_inner_smul_left, radianFourier_scaled, smul_eq_mul, cycleFrequencySymbol, tau]

/-- Entrywise action for the full matrix symbol in the manuscript convention. -/
def radianMatrixFirstOrderAction {ι : Type*} [Fintype ι]
    (a : ι → ι → Space → Space → ℂ) (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) : ℂ :=
  ∑ j, radianFirstOrderAction (a i j) (f j) x

theorem radianMatrixFirstOrderAction_eq {ι : Type*} [Fintype ι]
    (a : ι → ι → Space → Space → ℂ) (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    radianMatrixFirstOrderAction a f i x = matrixFirstOrderAction (fun j k => cycleFrequencySymbol (a j k)) f i x := by
  simp only [radianMatrixFirstOrderAction, radianFirstOrderAction_eq, matrixFirstOrderAction]

theorem HormanderOrderOne.cycleFrequencySymbol {a : Space → Space → ℂ} (ha : HormanderOrderOne a) :
    HormanderOrderOne (cycleFrequencySymbol a) := by
  apply ha.frequencyDilation
  unfold tau
  linarith [Real.one_le_pi_div_two]

/-- The scalar-coefficient part of `lem:commutator` in the original Fourier
convention, with proper support of the actual kernel and symmetry of the actual action. -/
theorem originalRadianScalarLipschitzEnergy {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, HormanderOrderOne (a i j))
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (cycleFrequencySymbol (a i j))))
    (hSym : ∀ f g : ι → SchwartzMap Space ℂ,
      (∑ i, ∫ x, conj (g i x) * radianMatrixFirstOrderAction a f i x) =
        ∑ i, ∫ x, conj (radianMatrixFirstOrderAction a g i x) * f i x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → Space → ℂ),
      (∀ b d, ContDiff ℝ ∞ (r b d)) →
      (∀ b d x, conj (r b d x) = r b d x) →
      (∀ b d x, r b d x = r d b x) →
      let entries : Fin 4 × Fin 4 → Space → ℂ := fun i => r i.1 i.2
      HasFiniteCoordinateW1Infty entries → ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (radianMatrixFirstOrderAction a f.val i x) *
          compactScalarPrincipalField r f i x).im| ≤ C * coordinateW1Infty entries *
            (compactMatrixCoordinateH1 f)^2 := by
  have hCycleSym : MatrixFirstOrderFormalSymmetry (fun i j => cycleFrequencySymbol (a i j)) := by
    intro f g
    simpa only [radianMatrixFirstOrderAction_eq] using hSym f g
  simpa only [radianMatrixFirstOrderAction_eq] using originalScalarLipschitzEnergy
    (fun i j => (ha i j).cycleFrequencySymbol) hProper hCycleSym

/-- The Hermitian-coefficient part of `lem:commutator` in the original Fourier
convention, with the same scalar full symbol on each field component. -/
theorem originalRadianHermitianLipschitzEnergy {ι : Type*} [Fintype ι] {a : Space → Space → ℂ}
    (ha : HormanderOrderOne a) (hProper : ProperKernelRelation (firstOrderKernelRelation (cycleFrequencySymbol a)))
    (hSym : ∀ f g : SchwartzMap Space ℂ,
      (∫ x, conj (g x) * radianFirstOrderAction a f x) =
        ∫ x, conj (radianFirstOrderAction a g x) * f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin 4 → Fin 4 → ι → ι → Space → ℂ),
      (∀ b d i j, ContDiff ℝ ∞ (r b d i j)) →
      (∀ b d i j x, conj (r b d i j x) = r d b j i x) →
      let entries : Fin 4 × Fin 4 × ι × ι → Space → ℂ := fun i => r i.1 i.2.1 i.2.2.1 i.2.2.2
      HasFiniteCoordinateW1Infty entries → ∀ f : CompactSchwartzComponents ι,
        |2 * (∑ i, ∫ x, conj (radianFirstOrderAction a (f.val i) x) *
          compactFinitePrincipalField r f i x).im| ≤ C * coordinateW1Infty entries *
            (compactMatrixCoordinateH1 f)^2 := by
  have hCycleSym : FirstOrderFormalSymmetry (cycleFrequencySymbol a) := by
    intro g f
    simpa only [radianFirstOrderAction_eq] using hSym f g
  simpa only [radianFirstOrderAction_eq] using
    originalHermitianLipschitzEnergy (ι := ι) ha.cycleFrequencySymbol hProper hCycleSym

end Burnett.Analysis.CarlesonEmbedding
