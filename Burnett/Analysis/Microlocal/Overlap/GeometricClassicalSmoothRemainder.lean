import Burnett.Analysis.Microlocal.Overlap.ClassicalSymbolSmoothingAddition
import Burnett.Analysis.Microlocal.Overlap.LocalSmoothKernelCutoff
import Burnett.Analysis.Microlocal.Overlap.GeometricSymmetricJetWindowAdmission

/-! Ordinary local classical expansions with smooth kernels for the same bundle operator. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The ordinary classical chart expansion of the actual output row, including
a smooth remainder kernel on a neighbourhood of both window slots. -/
def HasLocalClassicalSymmetricJetExpansion (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M)
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ) : Prop :=
  ∀ (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target),
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ U ⊆ c.chart.target ∧
      ∃ p R : JetSlot → JetSlot → E → E → ℂ,
        (∀ i j, ContDiffOn ℝ ∞ (uncurry (p i j)) (U ×ˢ univ)) ∧
        (∀ i j, ContDiffOn ℝ ∞ (uncurry (R i j)) (U ×ˢ U)) ∧
        (∀ i j (L : Set E), IsCompact L → L ⊆ U → ∃ r₀ : ℝ,
          ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ ξ : E, r₀ ≤ ‖ξ‖ →
            (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => p i j y ξ - a c i j y ξ) x‖ ≤ C) ∧
        ∀ (i j : JetSlot) (w : SchwartzMap E ℂ) (hw : tsupport (w : E → ℂ) ⊆ K), ∀ x ∈ K,
          symmetricJetGramHalfDensityRow r B c
            (A (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single j w)
              (tsupport_singleSymmetricJetWindow_subset j w hw))) i x =
                firstOrderAction (p i j) w x + ∫ y, R i j x y * w y

/-- Choose compact smooth kernels for each window and absorb them into the
ordinary exact left symbol of the same operator. -/
theorem hasOrdinarySymmetricJetWindowSymbols_of_localClassicalExpansion
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M)
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ)
    (hPrincipal : ∀ (c : AtlasChart M) i j,
      ContDiffOn ℝ ∞ (uncurry (a c i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ (c : AtlasChart M) i j x, x ∈ c.chart.target → ∀ s : ℝ, 0 < s →
      ∀ ξ : E, ξ ≠ 0 → a c i j x (s • ξ) = a c i j x ξ)
    (hLocal : HasLocalClassicalSymmetricJetExpansion r B hB hn A a) :
    HasOrdinarySymmetricJetWindowSymbols r B hB hn A a := by
  intro c K hK hKc
  obtain ⟨U, hU, hKU, hUc, p, R, hP, hR, hOrder, hAction⟩ := hLocal c K hK hKc
  have hCompact (i j : JetSlot) := exists_compactSmoothKernel_eq_on_window U K hU hK hKU (R i j) (hR i j)
  choose S k hS hk hSupport hOn using hCompact
  let full (i j : JetSlot) (x ξ : E) :=
    p i j x ξ + displacementKernelLeftSymbol (fun y z => k i j y (y-z)) x ξ
  have hSum (i j : JetSlot) := classicalFullSymbol_add_compactSmoothKernel U hU (p i j) (a c i j) (k i j)
    (hP i j) ((hPrincipal c i j).mono (prod_mono hUc Subset.rfl))
    (fun x hx => hDegree c i j x (hUc hx)) (hOrder i j) (S i j) (S i j) (hS i j) (hS i j)
    (hk i j) (hSupport i j)
  refine ⟨U, hU, hKU, hUc, full, (fun i j => (hSum i j).1), (fun i j => (hSum i j).2.1), ?_⟩
  intro i j w hw x hx
  have hFull : firstOrderAction (full i j) w x = firstOrderAction (p i j) w x + ∫ y, k i j x y * w y :=
    (hSum i j).2.2 w x (hKU hx)
  rw [hAction i j w hw x hx, hFull, hOn i j w hw x hx]

end Burnett.Microlocal.Overlap
