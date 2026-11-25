import Burnett.Analysis.Microlocal.Overlap.SymmetricJetActualLocalSymbol
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetOverlapWeights

/-! The mixed chart identity needs agreement only on the two compact test windows. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AtlasOverlapKernel
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff InnerProduct Manifold Topology

open private compactWeightedSchwartz_tsupport from Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing
open private linearArrayPairing_eq_sum from Burnett.Analysis.Microlocal.Overlap.SymmetricJetActualLocalSymbol

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The actual form and a matrix of operators agree when both tests are
supported in the indicated compact chart window. -/
def HasSupportedSymmetricJetOperatorEntries
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (Q : SymmetricJetGlobalForm M) (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (T : JetSlot → JetSlot → ComplexL2 E →L[ℂ] ComplexL2 E) : Prop :=
  ∀ (i j : JetSlot) (f w : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ K) (hw : tsupport (w : E → ℂ) ⊆ K),
    inner ℂ (f.toLp 2 volume) (T i j (w.toLp 2 volume)) =
      Q (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f) (tsupport_singleSymmetricJetWindow_subset i f hf))
        (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single j w) (tsupport_singleSymmetricJetWindow_subset j w hw))

private theorem supportedSymmetricJetOperatorEntries_pairing_array
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (Q : SymmetricJetGlobalForm M) (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (T : JetSlot → JetSlot → ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasSupportedSymmetricJetOperatorEntries B hB hn Q c K hK hKc T)
    (f w : JetSlot → SchwartzMap E ℂ) (hf : ∀ i, tsupport (f i : E → ℂ) ⊆ K)
    (hw : ∀ j, tsupport (w j : E → ℂ) ⊆ K) :
    Q (supportedSymmetricJetChartTest B hB hn c K hK hKc f hf)
      (supportedSymmetricJetChartTest B hB hn c K hK hKc w hw) =
        ∑ i, ∑ j, inner ℂ ((f i).toLp 2 volume) (T i j ((w j).toLp 2 volume)) := by
  obtain ⟨J, _, _, hJU, α, hα, hαC, hαS, _, hαK⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK c.chart.open_target hKc
  let ρ : D := ⟨α, hα, hαC⟩
  have hρ : tsupport (ρ : E → ℝ) ⊆ c.chart.target := hαS.trans hJU
  let L := compactSymmetricJetChartTestLinear B hB hn c ρ hρ
  have hL (u : JetSlot → SchwartzMap E ℂ) (hu : ∀ i, tsupport (u i : E → ℂ) ⊆ K) :
      L u = supportedSymmetricJetChartTest B hB hn c K hK hKc u hu :=
    compactSymmetricJetChartTestLinear_eq_supported B hB hn c K hK hKc ρ hρ hαK u hu
  rw [← hL f hf, ← hL w hw, linearArrayPairing_eq_sum Q L L f w]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hL _ (tsupport_singleSymmetricJetWindow_subset i (f i) (hf i)),
    hL _ (tsupport_singleSymmetricJetWindow_subset j (w j) (hw j))]
  exact (hT i j (f i) (w j) (hf i) (hw j)).symm

/-- Actual bilateral matrix change between two compact windows of one form. -/
theorem supportedSymmetricJetOperatorEntries_pairing_change
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (Q : SymmetricJetGlobalForm M) (c d : AtlasChart M)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) (hKc : K ⊆ c.chart.target)
    (hK' : IsCompact (c.transition d '' K)) (hK'd : c.transition d '' K ⊆ d.chart.target)
    (C D : JetSlot → JetSlot → ComplexL2 E →L[ℂ] ComplexL2 E)
    (hC : HasSupportedSymmetricJetOperatorEntries B hB hn Q c K hK hKc C)
    (hD : HasSupportedSymmetricJetOperatorEntries B hB hn Q d (c.transition d '' K) hK' hK'd D)
    (u : JetSlot → JetSlot → E → ℂ) (hu : ∀ i j, ContDiff ℝ ∞ (u i j))
    (hU : ∀ i j x, x ∈ K → u i j x = receivingJetOverlapWeight c d i j x)
    (i j : JetSlot) (f w : SchwartzMap E ℂ)
    (hfc : HasCompactSupport (f : E → ℂ)) (hwc : HasCompactSupport (w : E → ℂ))
    (hf : tsupport (f : E → ℂ) ⊆ K) (hw : tsupport (w : E → ℂ) ⊆ K) :
    let F (k : JetSlot) := transportedHalfDensitySchwartz c d K hK hKU
      (compactWeightedSchwartz (u k i) (hu k i) f hfc) ((compactWeightedSchwartz_tsupport _ _ _ _).trans hf)
    let W (k : JetSlot) := transportedHalfDensitySchwartz c d K hK hKU
      (compactWeightedSchwartz (u k j) (hu k j) w hwc) ((compactWeightedSchwartz_tsupport _ _ _ _).trans hw)
    inner ℂ (f.toLp 2 volume) (C i j (w.toLp 2 volume)) =
      ∑ k, ∑ l, inner ℂ ((F k).toLp 2 volume) (D k l ((W l).toLp 2 volume)) := by
  intro F W
  have hF (k : JetSlot) : tsupport (F k : E → ℂ) ⊆ c.transition d '' K :=
    (transportedHalfDensity_smooth_compact_support c d K hK hKU
      (compactWeightedSchwartz (u k i) (hu k i) f hfc) ((compactWeightedSchwartz_tsupport _ _ _ _).trans hf)).2.2
  have hW (k : JetSlot) : tsupport (W k : E → ℂ) ⊆ c.transition d '' K :=
    (transportedHalfDensity_smooth_compact_support c d K hK hKU
      (compactWeightedSchwartz (u k j) (hu k j) w hwc) ((compactWeightedSchwartz_tsupport _ _ _ _).trans hw)).2.2
  rw [hC i j f w hf hw,
    supportedSymmetricJetChartTest_single_eq_transport B hB hn c d K hK hKU hKc hK'd hK' u hu hU i f hfc hf,
    supportedSymmetricJetChartTest_single_eq_transport B hB hn c d K hK hKU hKc hK'd hK' u hu hU j w hwc hw]
  exact supportedSymmetricJetOperatorEntries_pairing_array B hB hn Q d (c.transition d '' K) hK' hK'd D hD F W hF hW

end Burnett.Microlocal.Overlap
