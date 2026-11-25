import Burnett.Analysis.Microlocal.Overlap.CompactSymmetricJetWindowData
import Burnett.Analysis.Microlocal.Overlap.CompactAngularPrincipalRegularity
import Burnett.Analysis.Microlocal.Overlap.SupportedSymmetricJetOperatorEntries
import Burnett.Analysis.Microlocal.Overlap.ReceivingRegularScalarTransport

/-! The same form determines its principal congruence from compact chart windows. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AtlasOverlapKernel
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

open private compactWeightedSchwartz_tsupport from Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Each actual chart expression is used only on its own compact window.
Equality of the underlying two-sided form identifies their principal symbols. -/
theorem compactSymmetricJetWindowData_principal_change
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (Q : SymmetricJetGlobalForm M) (c d : AtlasChart M)
    (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (hKc : K ⊆ c.chart.target) (hK' : IsCompact (c.transition d '' K))
    (hK'd : c.transition d '' K ⊆ d.chart.target)
    (a b : JetSlot → JetSlot → E → E → ℂ)
    (P : CompactSymmetricJetWindowData B hB hn Q c a K hK hKc)
    (R : CompactSymmetricJetWindowData B hB hn Q d b (c.transition d '' K) hK' hK'd)
    (x : E) (hx : x ∈ interior L) (ξ : E) (hξ : ξ ≠ 0) (i j : JetSlot) :
    let hSrc := hKU (interior_subset (hLK (interior_subset hx)))
    a i j x ξ = ∑ k : JetSlot, ∑ l : JetSlot,
      conj (receivingJetOverlapWeight c d k i x) *
        b k l (c.transition d x) (frozenChartFrequency c d hSrc ξ) *
          receivingJetOverlapWeight c d l j x := by
  intro hSrc
  have hLK' := hLK.trans interior_subset
  obtain ⟨C, hC⟩ := exists_compactSymmetricJetWindowOperators P
  obtain ⟨D, hD⟩ := exists_compactSymmetricJetWindowOperators R
  have hCPair : HasSupportedSymmetricJetOperatorEntries B hB hn Q c K hK hKc C :=
    fun i j f w hf hw => ((hC i j).2 f w hf hw).symm
  have hDPair : HasSupportedSymmetricJetOperatorEntries B hB hn Q d (c.transition d '' K) hK' hK'd D :=
    fun k l f w hf hw => ((hD k l).2 f w hf hw).symm
  obtain ⟨u, hu, hU⟩ := exists_smoothReceivingJetOverlapWeights c d K hK hKU
  have hEach (k l : JetSlot) := exists_receivingJointClassicalOperator_of_representation_with_regular_principal
    c d K L hK hL hLK hKU hConv (R.principal k l) R.baseSupport R.baseSupport_compact
    (R.principal_support k l) (R.principal_smooth k l) (R.principal_zero_smooth k l) (R.principal_degree k l)
    (D k l) (hD k l).1
  choose η T hTransport using hEach
  let p (k l : JetSlot) := receivingJointSymbol c d (physicalCoefficient (η k l)) (R.principal k l)
  have hReg (k l : JetSlot) : HasAngularPrincipalRegularity (p k l) := (hTransport k l).2.2.2.1
  have hRep (k l : JetSlot) : HasLocalClassicalRepresentation (T k l) (p k l) L :=
    (hTransport k l).2.2.2.2.1
  have hCReg : HasAngularPrincipalRegularity (P.principal i j) :=
    hasAngularPrincipalRegularity_of_compactSmooth _ P.baseSupport P.baseSupport_compact (P.principal_support i j)
      (P.principal_smooth i j) (P.principal_zero_smooth i j) (P.principal_degree i j)
  have hCRep : HasLocalClassicalRepresentation (C i j) (P.principal i j) L := by
    obtain ⟨E₀, hE₀, hAct⟩ := (hC i j).1
    exact ⟨E₀, hE₀, fun f w hw => hAct f w (hw.trans hLK')⟩
  have hMix (f w : SchwartzMap E ℂ) (hfc : HasCompactSupport (f : E → ℂ))
      (hwc : HasCompactSupport (w : E → ℂ)) (hf : tsupport (f : E → ℂ) ⊆ L)
      (hw : tsupport (w : E → ℂ) ⊆ L) :
      inner ℂ (f.toLp 2 volume) (C i j (w.toLp 2 volume)) =
        ∑ k : JetSlot, ∑ l : JetSlot,
          inner ℂ ((compactWeightedSchwartz (u k i) (hu k i) f hfc).toLp 2 volume)
            (T k l ((compactWeightedSchwartz (u l j) (hu l j) w hwc).toLp 2 volume)) := by
    have hEq := supportedSymmetricJetOperatorEntries_pairing_change B hB hn Q c d K hK hKU hKc
      hK' hK'd C D hCPair hDPair u hu hU i j f w hfc hwc (hf.trans hLK') (hw.trans hLK')
    refine hEq.trans (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_)))
    exact (hTransport k l).2.2.2.2.2
      (compactWeightedSchwartz (u l j) (hu l j) w hwc)
      (compactWeightedSchwartz (u k i) (hu k i) f hfc)
      ((compactWeightedSchwartz_tsupport _ _ _ _).trans hw) ((compactWeightedSchwartz_tsupport _ _ _ _).trans hf)
  have hLocal := eqOn_interior_principalSymbol_of_bilateralWeightedPairings (C i j) T
    (P.principal i j) p (fun k => u k i) (fun l => u l j) (fun k => hu k i) (fun l => hu l j)
    L hCRep hRep hCReg hReg hMix ξ hξ hx
  have hxL : x ∈ L := interior_subset hx
  have hxK : x ∈ K := hLK' hxL
  have hFreq : frozenChartFrequency c d hSrc ξ ≠ 0 := by
    intro h
    exact hξ ((frozenChartFrequency c d hSrc).injective (h.trans (map_zero _).symm))
  have hR (k l : JetSlot) :
      p k l x ξ = b k l (c.transition d x) (frozenChartFrequency c d hSrc ξ) :=
    ((hTransport k l).2.2.1 x hxL ξ).trans
      (R.principal_eq k l _ (mem_image_of_mem _ hxK) _ hFreq)
  change P.principal i j x ξ = ∑ k : JetSlot, ∑ l : JetSlot,
    conj (u k i x) * p k l x ξ * u l j x at hLocal
  rw [P.principal_eq i j x hxK ξ hξ] at hLocal
  simpa only [hU _ _ x hxK, hR] using hLocal

end Burnett.Microlocal.Overlap
