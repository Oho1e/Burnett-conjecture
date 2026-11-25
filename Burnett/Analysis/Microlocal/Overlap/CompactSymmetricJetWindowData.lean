import Burnett.Analysis.Microlocal.Overlap.SymmetricJetSupportedChartTest
import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization

/-! One compact chart window supplies actual classical entries of a global form. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

/-- Inserting one Schwartz test into the ordered jet slots preserves its window. -/
theorem tsupport_singleSymmetricJetWindow_subset (i : JetSlot) (f : SchwartzMap E ℂ)
    {K : Set E} (hf : tsupport (f : E → ℂ) ⊆ K) (j : JetSlot) :
    tsupport ((Pi.single i f : JetSlot → SchwartzMap E ℂ) j : E → ℂ) ⊆ K := by
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same]
    exact hf
  · rw [Pi.single_eq_of_ne h, SchwartzMap.coe_zero]
    simp [tsupport]

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Symbols for a single compact window, with exact action on window-supported
sections and a fixed chart principal on its nonzero frequencies. -/
structure CompactSymmetricJetWindowData
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (Q : SymmetricJetGlobalForm M) (c : AtlasChart M) (a : JetSlot → JetSlot → E → E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target) where
  full : JetSlot → JetSlot → E → E → ℂ
  principal : JetSlot → JetSlot → E → E → ℂ
  baseSupport : Set E
  baseSupport_compact : IsCompact baseSupport
  full_support : ∀ i j ξ, tsupport (fun x => full i j x ξ) ⊆ baseSupport
  principal_support : ∀ i j ξ, tsupport (fun x => principal i j x ξ) ⊆ baseSupport
  full_smooth : ∀ i j, ContDiff ℝ ∞ (uncurry (full i j))
  principal_smooth : ∀ i j, ContDiffOn ℝ ∞ (uncurry (principal i j)) (univ ×ˢ ({0}ᶜ : Set E))
  principal_zero_smooth : ∀ i j, ContDiff ℝ ∞ (fun x => principal i j x 0)
  principal_degree : ∀ i j x, DegreeZero (principal i j x)
  principal_eq : ∀ i j x, x ∈ K → ∀ ξ : E, ξ ≠ 0 → principal i j x ξ = a i j x ξ
  order_minus_one : ∀ i j, ∃ R : ℝ, ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => full i j y ξ - principal i j y ξ) x‖ ≤ C
  action : ∀ (i j : JetSlot) (f w : SchwartzMap E ℂ)
    (hf : tsupport (f : E → ℂ) ⊆ K) (hw : tsupport (w : E → ℂ) ⊆ K),
    Q (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f)
        (tsupport_singleSymmetricJetWindow_subset i f hf))
      (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single j w)
        (tsupport_singleSymmetricJetWindow_subset j w hw)) = classicalLeftPairing (full i j) f w

/-- Each fixed-window matrix entry gives a bounded operator with the actual
principal representation and the same bilateral pairing on supported tests. -/
theorem exists_compactSymmetricJetWindowOperators
    {B : Field (M := M)} {hB : IsSmooth B} {hn : IsNondegenerate B}
    {Q : SymmetricJetGlobalForm M} {c : AtlasChart M} {a : JetSlot → JetSlot → E → E → ℂ}
    {K : Set E} {hK : IsCompact K} {hKc : K ⊆ c.chart.target}
    (W : CompactSymmetricJetWindowData B hB hn Q c a K hK hKc) :
    ∃ T : JetSlot → JetSlot → ComplexL2 E →L[ℂ] ComplexL2 E, ∀ i j,
      HasLocalClassicalRepresentation (T i j) (W.principal i j) K ∧
      ∀ (f w : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ K) (hw : tsupport (w : E → ℂ) ⊆ K),
        Q (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f)
            (tsupport_singleSymmetricJetWindow_subset i f hf))
          (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single j w)
            (tsupport_singleSymmetricJetWindow_subset j w hw)) =
          inner ℂ (f.toLp 2 volume) (T i j (w.toLp 2 volume)) := by
  classical
  have hEntry (i j : JetSlot) := exists_classicalFullSymbolOperator (W.full i j) (W.principal i j)
    W.baseSupport W.baseSupport_compact (W.full_support i j) (W.principal_support i j)
    (W.full_smooth i j) (W.principal_smooth i j) (W.principal_zero_smooth i j) (W.principal_degree i j)
    (W.order_minus_one i j).choose (W.order_minus_one i j).choose_spec
  choose T hPair hRep using hEntry
  exact ⟨T, fun i j => ⟨hRep i j K hK, fun f w hf hw =>
    (W.action i j f w hf hw).trans ((hPair i j f w).symm)⟩⟩

end Burnett.Microlocal.Overlap
