import Burnett.Analysis.Microlocal.Overlap.GeometricSymmetricJetOperatorForm
import Burnett.Analysis.Microlocal.Overlap.CompactSymmetricJetWindowData

/-! Recover the Gram-weighted coordinate action from the single bundle operator. -/
set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 8500000
set_option synthInstance.maxHeartbeats 430000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter Matrix MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ComplexConjugate ContDiff Manifold Topology

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The coordinate column obtained by projecting an ordered unit slot to the
actual symmetric subspace. -/
def symmetricJetProjectedSlot (i k : JetSlot) : ℂ :=
  (2 : ℂ)⁻¹ * ((Pi.single i (1 : ℂ) : JetSlot → ℂ) k +
    (Pi.single i (1 : ℂ) : JetSlot → ℂ) (jetPairSwap k))

omit [SecondCountableTopology M] in
theorem symmetricJetComponent_chartColumn_of_mem (c : AtlasChart M) (i k : JetSlot)
    (p : M) (hp : p ∈ c.chart.source) :
    symmetricJetComponent c (fun x => symmetricJetChartColumn c i x) k p =
      symmetricJetProjectedSlot i k := by
  rw [symmetricJetComponent_of_mem c _ k p hp]
  unfold symmetricJetChartColumn
  rw [dif_pos hp]
  unfold projectedJetColumn
  rw [jetFiberCoordinates_projectComplexSymmetricJet, LinearEquiv.apply_symm_apply]
  rfl

/-- The unpaired endomorphism kernel in the two physical chart frames. -/
def symmetricJetLinearKernelEntry (K : SymmetricJetLinearKernel M) (c d : AtlasChart M)
    (i j : JetSlot) (p q : M) : ℂ :=
  symmetricJetComponent c (fun x => K x q (symmetricJetChartColumn d j q)) i p

theorem continuousOn_pairSymmetricJetLinearKernelEntry (r : Metric (M := M)) (K : SymmetricJetLinearKernel M)
    (c d : AtlasChart M) (S T : Set M) (hS : S ⊆ c.chart.source)
    (hK : ∀ i j, ContinuousOn (uncurry (symmetricJetLinearKernelEntry K c d i j)) (S ×ˢ T))
    (i j : JetSlot) :
    ContinuousOn (uncurry (symmetricJetKernelEntry (pairSymmetricJetLinearKernel r K) c d i j)) (S ×ˢ T) := by
  let F (z : M × M) := ∑ l, conj (symmetricJetProjectedSlot i l) *
    (∑ k, atlasJetGram r c z.1 l k * symmetricJetLinearKernelEntry K c d k j z.1 z.2)
  have hF : ContinuousOn F (S ×ˢ T) := by
    refine continuousOn_finset_sum _ fun l _ => continuousOn_const.mul ?_
    refine continuousOn_finset_sum _ fun k _ => ?_
    exact ((continuousOn_atlasJetGram_entry r c l k).comp continuous_fst.continuousOn
      (fun _ hz => hS hz.1)).mul (hK k j)
  refine hF.congr ?_
  rintro ⟨p, q⟩ hpq
  have hp : p ∈ c.chart.source := hS hpq.1
  change symmetricJetFiberGram r p (symmetricJetChartColumn c i p)
    (K p q (symmetricJetChartColumn d j q)) = F (p, q)
  rw [symmetricJetFiberGram_section_eq_components r c (fun x => symmetricJetChartColumn c i x)
    (fun x => K x q (symmetricJetChartColumn d j q)) p hp]
  simp only [F, symmetricJetComponent_chartColumn_of_mem c i _ p hp, symmetricJetLinearKernelEntry]

/-- The output half-density row paired against the actual projected ordered
unit slot, with the same auxiliary Gram as the intrinsic pairing. -/
def symmetricJetGramHalfDensityRow (r : Metric (M := M)) (B : Field (M := M))
    (c : AtlasChart M) (u : SymmetricJetSection M) (i : JetSlot) (x : E) : ℂ :=
  ∑ k, conj (symmetricJetProjectedSlot i k) *
    (∑ j, atlasJetGram r c (c.chart.symm x) k j * symmetricJetHalfDensity B c u j x)

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem geometricSymmetricJetOperatorForm_eq_chartPairing_of_support
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M) (hA : ∀ u, IsSmoothSymmetricJetSection (A u))
    (c : AtlasChart M) (v u : smoothCompactSymmetricJet M)
    (hv : symmetricJetSectionSupport v.val ⊆ c.chart.source) :
    geometricSymmetricJetOperatorForm r B hB A hA v u =
      ∫ x in c.chart.target, ∑ i, conj (symmetricJetHalfDensity B c v.val i x) *
        (∑ j, atlasJetGram r c (c.chart.symm x) i j * symmetricJetHalfDensity B c (A u) j x) := by
  let μ := ManifoldVolume.geometricMeasure B
  let g (p : M) := symmetricJetFiberGram r p (v.val p) (A u p)
  have hg : Continuous g := continuous_symmetricJetFiberGram_sections r v.val (A u) v.property.1 (hA u)
  have hgSupp : support g ⊆ c.chart.source := by
    intro p hp
    apply hv
    intro hz
    exact hp (by simp [g, hz])
  change (∫ p, g p ∂μ) = _
  have hR : (∫ p, g p ∂μ) = ∫ p in c.chart.source, g p ∂μ := by
    rw [← integral_indicator c.chart.open_source.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      by_cases hp : p ∈ c.chart.source
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp, notMem_support.mp (fun h => hp (hgSupp h))]
  rw [hR, integral_geometricVolume_receiving B hB c g hg.stronglyMeasurable]
  apply setIntegral_congr_fun c.chart.open_target.measurableSet
  intro x hx
  change (fixedHalfDensity B c x ^ 2) • symmetricJetFiberGram r (c.chart.symm x) (v.val (c.chart.symm x))
    (A u (c.chart.symm x)) = _
  rw [symmetricJetFiberGram_section_eq_components r c v.val (A u) _ (c.chart.symm_mapsTo hx)]
  simp only [symmetricJetHalfDensity, receivingScalarTestHalfDensity, indicator_of_mem hx,
    Complex.real_smul, Complex.ofReal_pow, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Turning a single real-bundle test column into a scalar Schwartz pairing
uses the actual volume and Gram. The operator is still the one global A. -/
theorem geometricSymmetricJetOperatorForm_eq_single_chartRow
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M) (hA : ∀ u, IsSmoothSymmetricJetSection (A u))
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (i : JetSlot) (f : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ K) (u : smoothCompactSymmetricJet M) :
    geometricSymmetricJetOperatorForm r B hB A hA
      (supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f)
        (tsupport_singleSymmetricJetWindow_subset i f hf)) u =
      ∫ x, conj (f x) * symmetricJetGramHalfDensityRow r B c (A u) i x := by
  let v := supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f)
    (tsupport_singleSymmetricJetWindow_subset i f hf)
  change geometricSymmetricJetOperatorForm r B hB A hA v u = _
  have hv : symmetricJetSectionSupport v.val ⊆ c.chart.source :=
    (symmetricJetChartLift_support B c _ K (fun j =>
      (subset_tsupport _).trans (tsupport_singleSymmetricJetWindow_subset i f hf j))).trans
      ((c.chart.symm_mapsTo.mono_left hKc).image_subset)
  rw [geometricSymmetricJetOperatorForm_eq_chartPairing_of_support r B hB A hA c v u hv,
    ← integral_indicator c.chart.open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ c.chart.target
  · rw [indicator_of_mem hx]
    have hRead (k : JetSlot) : symmetricJetHalfDensity B c v.val k x = symmetricJetProjectedSlot i k * f x := by
      change symmetricJetHalfDensity B c (symmetricJetChartLift B c _) k x = _
      rw [symmetricJetHalfDensity_chartLift_of_mem B hn c _ k x hx]
      have hSingle (j : JetSlot) : ((Pi.single i f : JetSlot → SchwartzMap E ℂ) j) x =
          (Pi.single i (1 : ℂ) : JetSlot → ℂ) j * f x := by
        by_cases hji : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne hji]
      simp only [hSingle, symmetricJetProjectedSlot]
      ring
    simp only [hRead, symmetricJetGramHalfDensityRow, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (f := (f : E → ℂ))
      (fun hs => hx (hKc (hf hs)))
    rw [indicator_of_notMem hx, hz, map_zero, zero_mul]

end Burnett.Microlocal.Overlap
