import Burnett.Analysis.Microlocal.Overlap.GeometricSymmetricJetChartAction
import Burnett.Analysis.Microlocal.Overlap.WindowedClassicalSymmetricJetForm
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! Admit the ordinary pointwise chart representations of one geometric
operator to the compact-window defect-test interface. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 9000000
set_option synthInstance.maxHeartbeats 450000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff Manifold Topology

open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal
open private leftCutoff_exteriorBounds from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- A pointwise left Fourier symbol for the actual Gram-weighted output row
on each compact chart window. The symbol only needs to be smooth on an open
neighbourhood of the window. The input is a genuine supported test column. -/
def HasOrdinarySymmetricJetWindowSymbols (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M)
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ) : Prop :=
  ∀ (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target),
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ U ⊆ c.chart.target ∧
      ∃ b : JetSlot → JetSlot → E → E → ℂ,
        (∀ i j, ContDiffOn ℝ ∞ (uncurry (b i j)) (U ×ˢ univ)) ∧
        (∀ i j (L : Set E), IsCompact L → L ⊆ U → ∃ R : ℝ,
          ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ ξ : E, R ≤ ‖ξ‖ →
            (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => b i j y ξ - a c i j y ξ) x‖ ≤ C) ∧
        ∀ (i j : JetSlot) (w : SchwartzMap E ℂ) (hw : tsupport (w : E → ℂ) ⊆ K), ∀ x ∈ K,
          symmetricJetGramHalfDensityRow r B c
            (A (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single j w)
              (tsupport_singleSymmetricJetWindow_subset j w hw))) i x = firstOrderAction (b i j) w x

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- Build the compactly based full and principal symbols by a genuine left
plateau. The existing fixed-infrared quantization can then consume the window. -/
theorem exists_compactSymmetricJetWindowData_of_ordinarySymbols
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M) (hA : ∀ u, IsSmoothSymmetricJetSection (A u))
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ)
    (hPrincipal : ∀ (c : AtlasChart M) i j,
      ContDiffOn ℝ ∞ (uncurry (a c i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ (c : AtlasChart M) i j x, x ∈ c.chart.target → ∀ s : ℝ, 0 < s →
      ∀ ξ : E, ξ ≠ 0 → a c i j x (s • ξ) = a c i j x ξ)
    (hLocal : HasOrdinarySymmetricJetWindowSymbols r B hB hn A a)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target) :
    Nonempty (CompactSymmetricJetWindowData B hB hn
      (geometricSymmetricJetOperatorForm r B hB A hA) c (a c) K hK hKc) := by
  classical
  obtain ⟨U, hU, hKU, hUc, b, hb, hLarge, hAction⟩ := hLocal c K hK hKc
  obtain ⟨L, _, _, hLU, χ, hχ, hχc, hχL, _, hOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK hU hKU
  let θ : D := ⟨χ, hχ, hχc⟩
  have hθ : tsupport (θ : E → ℝ) ⊆ U := hχL.trans hLU
  let a₀ (i j : JetSlot) (x ξ : E) := if ξ = 0 then 0 else a c i j x ξ
  have ha₀ (i j : JetSlot) : ContDiffOn ℝ ∞ (uncurry (a₀ i j)) (U ×ˢ ({0}ᶜ : Set E)) := by
    apply ((hPrincipal c i j).mono (prod_mono hUc Subset.rfl)).congr
    intro z hz
    have hz0 : z.2 ≠ 0 := hz.2
    simp [uncurry, a₀, hz0]
  have haZero (i j : JetSlot) : ContDiffOn ℝ ∞ (fun x => a₀ i j x 0) U := by
    simpa only [a₀, if_pos rfl] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  have haDegree (i j : JetSlot) (x : E) (hx : x ∈ U) : DegreeZero (a₀ i j x) := by
    intro s hs ξ
    by_cases hξ : ξ = 0
    · simp [a₀, hξ]
    · simp only [a₀, if_neg (smul_ne_zero hs.ne' hξ), if_neg hξ]
      exact hDegree c i j x (hUc hx) s hs ξ hξ
  refine ⟨{
    full := fun i j => leftCutoffClassicalSymbol θ (b i j)
    principal := fun i j => leftCutoffClassicalSymbol θ (a₀ i j)
    baseSupport := tsupport (θ : E → ℝ)
    baseSupport_compact := test_compactSupport θ
    full_support := fun i j => leftCutoffClassicalSymbol_support θ (b i j)
    principal_support := fun i j => leftCutoffClassicalSymbol_support θ (a₀ i j)
    full_smooth := fun i j => ?_
    principal_smooth := fun i j => leftCutoffClassicalSymbol_smoothOn θ hU isOpen_compl_singleton hθ (ha₀ i j)
    principal_zero_smooth := fun i j => leftCutoffClassicalSymbol_smoothZero θ hU hθ (haZero i j)
    principal_degree := fun i j => leftCutoffClassicalSymbol_degreeZero θ hθ (haDegree i j)
    principal_eq := fun i j x hx ξ hξ => ?_
    order_minus_one := fun i j => ?_
    action := fun i j f w hf hw => ?_ }⟩
  · simpa only [univ_prod_univ, contDiffOn_univ] using
      leftCutoffClassicalSymbol_smoothOn θ hU isOpen_univ hθ (hb i j)
  · simp [leftCutoffClassicalSymbol, physicalCoefficient, θ, hOne x hx, a₀, hξ]
  · obtain ⟨R, hR⟩ := hLarge i j (tsupport (θ : E → ℝ)) (test_compactSupport θ) hθ
    have hReg (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (θ : E → ℝ), ∀ ξ : E, max 1 R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => b i j y ξ - a₀ i j y ξ) x‖ ≤ C := by
      obtain ⟨C, hC, hBound⟩ := hR m
      refine ⟨C, hC, fun x hx ξ hξ => ?_⟩
      have hξ0 : ξ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le ((le_max_left 1 R).trans hξ))
      simpa only [a₀, if_neg hξ0] using hBound x hx ξ ((le_max_right 1 R).trans hξ)
    exact ⟨_, leftCutoff_exteriorBounds θ hU hθ (hb i j) (ha₀ i j) (max 1 R) hReg⟩
  · rw [geometricSymmetricJetOperatorForm_eq_single_chartRow r B hB hn A hA c K hK hKc i f hf]
    unfold classicalLeftPairing
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [hAction i j w hw x hx]
      change conj (f x) * firstOrderAction (b i j) w x =
        conj (f x) * firstOrderAction (fun y ξ => physicalCoefficient θ y * b i j y ξ) w x
      rw [firstOrderAction_mul_base]
      simp [physicalCoefficient, θ, hOne x hx]
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (f := (f : E → ℂ)) (fun h => hx (hf h))
      rw [hz, map_zero, zero_mul, zero_mul]

/-- One geometric section operator yields a windowed form from its ordinary
pointwise local symbols and its off-diagonal endomorphism kernel. -/
def windowedClassicalSymmetricJetForm_of_geometricOperator
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M) (hA : ∀ u, IsSmoothSymmetricJetSection (A u))
    (a : AtlasChart M → JetSlot → JetSlot → E → E → ℂ)
    (hPrincipal : ∀ (c : AtlasChart M) i j,
      ContDiffOn ℝ ∞ (uncurry (a c i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ (c : AtlasChart M) i j x, x ∈ c.chart.target → ∀ s : ℝ, 0 < s →
      ∀ ξ : E, ξ ≠ 0 → a c i j x (s • ξ) = a c i j x ξ)
    (hLocal : HasOrdinarySymmetricJetWindowSymbols r B hB hn A a)
    (K : SymmetricJetLinearKernel M)
    (hKernel : ∀ (T : Set M), IsCompact T → ∀ (u : smoothCompactSymmetricJet M),
      symmetricJetSectionSupport u.val ⊆ T → ∀ p ∉ T, ∀ v : SymmetricJetFiber M p,
        symmetricJetFiberGram r p v (A u p) =
          ∫ q in T, pairSymmetricJetLinearKernel r K p q v (u.val q) ∂ManifoldVolume.geometricMeasure B)
    (hK : ∀ (c d : AtlasChart M) (S T : Set M), IsCompact S → IsCompact T →
      S ⊆ c.chart.source → T ⊆ d.chart.source → Disjoint S T →
      ∀ i j, ContinuousOn (uncurry (symmetricJetLinearKernelEntry K c d i j)) (S ×ˢ T)) :
    WindowedClassicalSymmetricJetForm B hB hn (geometricSymmetricJetOperatorForm r B hB A hA) where
  principal := a
  window := exists_compactSymmetricJetWindowData_of_ordinarySymbols r B hB hn A hA a hPrincipal hDegree hLocal
  kernel := pairSymmetricJetLinearKernel r K
  separated_action := geometricSymmetricJetOperatorForm_hasSeparatedKernel r B hB A hA K hKernel
  kernel_continuous := fun c d S T hS hT hc hd hST =>
    continuousOn_pairSymmetricJetLinearKernelEntry r K c d S T hc (hK c d S T hS hT hc hd hST)

end Burnett.Microlocal.Overlap
