import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal

/-! Realize an open-chart full symbol after a compact left cutoff. -/
set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 3400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set MeasureTheory Burnett.Fourier Burnett.Geometry ConnectionDifference
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ContDiff InnerProduct Topology

open private angularPrincipalZeroExtension
  from Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal
open private leftCutoff_exteriorBounds
  from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

local notation "E" => CoordinateSpace

/-- The local symbol itself supplies the bounded operator for the left-cutoff
pairing. Only the punctured principal data enter the assumptions. -/
theorem exists_compactLeftClassicalOperator
    (U : Set E) (hU : IsOpen U) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ U)
    (b a : E → E → ℂ)
    (hb : ContDiffOn ℝ ∞ (uncurry b) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ x ∈ U, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (R : ℝ) (hR : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (χ : E → ℝ), ∀ ξ : E,
      R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ f v : SchwartzMap E ℂ, inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        classicalLeftPairing (leftCutoffClassicalSymbol χ b) f v) ∧
      (∀ L : Set E, IsCompact L → HasLocalClassicalRepresentation T
        (leftCutoffClassicalSymbol χ (angularPrincipalZeroExtension a)) L) ∧
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, max 1 R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n
          (fun y => leftCutoffClassicalSymbol χ b y ξ - leftCutoffClassicalSymbol χ a y ξ) x‖ ≤ C) := by
  let a₀ := angularPrincipalZeroExtension a
  have hEq (x : E) (ξ : E) (hξ : ξ ≠ 0) : a₀ x ξ = a x ξ := by
    simp [a₀, angularPrincipalZeroExtension, hξ]
  have hDiff : ContDiffOn ℝ ∞ (uncurry a₀) (U ×ˢ ({0}ᶜ : Set E)) :=
    ha.congr fun z hz => hEq z.1 z.2 hz.2
  have hZero : ContDiffOn ℝ ∞ (fun x => a₀ x 0) U := by
    simpa only [a₀, angularPrincipalZeroExtension, if_pos rfl] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  have hDeg (x : E) (hx : x ∈ U) : DegreeZero (a₀ x) := by
    intro s hs ξ
    by_cases hξ : ξ = 0
    · rw [hξ, smul_zero]
    · rw [hEq _ _ (smul_ne_zero hs.ne' hξ), hEq _ _ hξ]
      exact hDegree x hx s hs ξ hξ
  have hB : ContDiff ℝ ∞ (uncurry (leftCutoffClassicalSymbol χ b)) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using
      leftCutoffClassicalSymbol_smoothOn χ hU isOpen_univ hχ hb
  have hLarge := leftCutoff_exteriorBounds χ hU hχ hb ha R hR
  have hLarge₀ : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, max 1 R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n
        (fun y => leftCutoffClassicalSymbol χ b y ξ - leftCutoffClassicalSymbol χ a₀ y ξ) x‖ ≤ C := by
    intro n
    obtain ⟨C, hC, hLim⟩ := hLarge n
    refine ⟨C, hC, fun x ξ hξ => ?_⟩
    have hnz : ξ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hξ))
    simpa only [leftCutoffClassicalSymbol, hEq _ _ hnz] using hLim x ξ hξ
  obtain ⟨T, hAct, hRep⟩ := exists_classicalFullSymbolOperator _ _ _ (test_compactSupport χ)
    (leftCutoffClassicalSymbol_support χ b) (leftCutoffClassicalSymbol_support χ a₀) hB
    (leftCutoffClassicalSymbol_smoothOn χ hU isOpen_compl_singleton hχ hDiff)
    (leftCutoffClassicalSymbol_smoothZero χ hU hχ hZero)
    (leftCutoffClassicalSymbol_degreeZero χ hχ hDeg) (max 1 R) hLarge₀
  exact ⟨T, hAct, hRep, hLarge⟩

end Burnett.Microlocal.Overlap
