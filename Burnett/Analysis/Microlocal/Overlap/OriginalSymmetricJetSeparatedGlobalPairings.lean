import Burnett.Analysis.Microlocal.Overlap.OriginalSymmetricJetTestSections
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetSeparatedChartPairing
import Burnett.Analysis.Microlocal.Overlap.CompactRectangleKernel
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantPairing

/-! Apply the actual global separated pairing to the original covariant jets. -/

set_option autoImplicit false
set_option maxHeartbeats 7800000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedHalfDensity fixedHalfDensity_smooth fixedVolumeCovariantGradientSchwartz
    fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped Manifold ContDiff Topology BigOperators ComplexConjugate

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The actual compactly supported global bundle form has zero limit on
separated windows of the true original covariant jet. -/
theorem tendsto_symmetricJetGlobalForm_originalSeparated
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (form : SymmetricJetGlobalForm M) (K : SymmetricJetPairingKernel M)
    (hForm : HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B) form K)
    (c d : AtlasChart M) (S T : Set M) (hS : IsCompact S) (hT : IsCompact T) (hST : Disjoint S T)
    (hSc : S ⊆ c.chart.source) (hTd : T ⊆ d.chart.source)
    (hK : ∀ i j, ContinuousOn (uncurry (symmetricJetKernelEntry K c d i j)) (S ×ˢ T))
    (χ η : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' S) (hη : tsupport (η : E → ℝ) ⊆ d.chart '' T) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hSc))
    let hηd := hη.trans (image_subset_iff.mpr (d.chart.mapsTo.mono_left hTd))
    Tendsto (fun n => form (originalCovariantSymmetricJetTest r B g hB hg hn c χ hχc n)
      (originalCovariantSymmetricJetTest r B g hB hg hn d η hηd n)) atTop (𝓝 0) := by
  intro hχc hηd
  let v := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχc
  let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn d η hηd
  let P := c.chart '' S
  let Q := d.chart '' T
  let k := symmetricJetWindowKernelEntry K c d S T
  let k' (i j : JetSlot) := receivingHalfDensityKernel B c d (k i j)
  have hP : IsCompact P := hS.image_of_continuousOn (c.chart.continuousOn.mono hSc)
  have hQ : IsCompact Q := hT.image_of_continuousOn (d.chart.continuousOn.mono hTd)
  have hpS : MapsTo c.chart.symm P S := by
    rintro _ ⟨p, hp, rfl⟩
    rwa [c.chart.left_inv (hSc hp)]
  have hqT : MapsTo d.chart.symm Q T := by
    rintro _ ⟨q, hq, rfl⟩
    rwa [d.chart.left_inv (hTd hq)]
  have hPt : P ⊆ c.chart.target := image_subset_iff.mpr (c.chart.mapsTo.mono_left hSc)
  have hQt : Q ⊆ d.chart.target := image_subset_iff.mpr (d.chart.mapsTo.mono_left hTd)
  have hPC : MapsTo (Prod.fst : E × E → E) (P ×ˢ Q) c.chart.target := fun _ hz => hPt hz.1
  have hQD : MapsTo (Prod.snd : E × E → E) (P ×ˢ Q) d.chart.target := fun _ hz => hQt hz.2
  have hKernel (i j : JetSlot) : ContinuousOn (uncurry (k' i j)) (P ×ˢ Q) := by
    have hRaw : ContinuousOn (uncurry (k i j)) (S ×ˢ T) :=
      (hK i j).congr fun z hz => indicator_of_mem hz _
    have hIn : ContinuousOn (fun z : E × E => (c.chart.symm z.1, d.chart.symm z.2)) (P ×ˢ Q) :=
      (c.chart.continuousOn_symm.comp continuous_fst.continuousOn hPC).prodMk
        (d.chart.continuousOn_symm.comp continuous_snd.continuousOn hQD)
    have hMap : MapsTo (fun z : E × E => (c.chart.symm z.1, d.chart.symm z.2)) (P ×ˢ Q) (S ×ˢ T) :=
      fun _ hz => ⟨hpS hz.1, hqT hz.2⟩
    have hδc := (Complex.continuous_ofReal.comp_continuousOn (fixedHalfDensity_smooth B hB hn c).continuousOn).comp
      continuous_fst.continuousOn hPC
    have hδd := (Complex.continuous_ofReal.comp_continuousOn (fixedHalfDensity_smooth B hB hn d).continuousOn).comp
      continuous_snd.continuousOn hQD
    exact (hδc.mul (hRaw.comp hIn hMap)).mul hδd
  obtain ⟨C, _, hV, _⟩ := fixedVolumeCovariantGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c χ hχc
  obtain ⟨D₀, _, hU, hWeak⟩ := fixedVolumeCovariantGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb d η hηd
  have hPair (i j : JetSlot) :
      Tendsto (fun n => ∫ x, conj (v n i x) * (∫ y, k' i j x y * u n j y)) atTop (𝓝 0) := by
    have hRect := continuous_compactRectangle_kernelPairing_tendsto_zero volume volume
      P Q hP hQ (k' i j) (hKernel i j)
      (fun n => (u n j : E → ℂ)) (fun n => (u n j).continuous.measurable) (fun n => (u n j).memLp 2 volume)
      (fun n => (v n i : E → ℂ)) (fun n => (v n i).memLp 2 volume) D₀ C
      (fun n => hU n j) (fun n => hV n i) (hWeak j)
    apply hRect.congr
    intro n
    rw [← integral_indicator hP.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ P
    · rw [indicator_of_mem hx, ← integral_indicator hQ.measurableSet]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Q
      · rw [indicator_of_mem hy]
      · have hz : u n j y = 0 := by
          by_contra h
          exact hy (hη (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn d η hηd n j
            (subset_tsupport _ h)))
        rw [indicator_of_notMem hy, hz, mul_zero]
    · have hz : v n i x = 0 := by
        by_contra h
        exact hx (hχ (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hχc n i
            (subset_tsupport _ h)))
      rw [indicator_of_notMem hx, hz, map_zero, zero_mul]
  have hSum (i : JetSlot) := tendsto_finset_sum Finset.univ (fun j _ => hPair i j)
  have hTotal : Tendsto (fun n => ∑ i, ∑ j, ∫ x, conj (v n i x) *
      (∫ y, k' i j x y * u n j y)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hSum i)
  apply hTotal.congr
  intro n
  rw [symmetricJetGlobalForm_eq_separatedChartPairings B hB form K hForm c d S T hS hT hST hSc hTd hK
    _ _ (originalCovariantSymmetricJetTest_support r B g hB hg hn c χ hχc S hSc hχ n)
    (originalCovariantSymmetricJetTest_support r B g hB hg hn d η hηd T hTd hη n)]
  simp only [originalCovariantSymmetricJetTest_halfDensity r B g hB hg hn hsB hsG, v, u, k', k]

end Burnett.Microlocal.Overlap
