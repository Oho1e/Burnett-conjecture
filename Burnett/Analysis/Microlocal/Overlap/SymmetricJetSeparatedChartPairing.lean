import Burnett.Analysis.Microlocal.Overlap.SymmetricJetPairingKernel
import Burnett.Analysis.Microlocal.Overlap.ReceivingPhysicalKernelTransport
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod

/-! The same global bundle pairing gives finite separated chart kernel pairings. -/

set_option autoImplicit false
set_option maxHeartbeats 7400000
set_option synthInstance.maxHeartbeats 380000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped Manifold ContDiff Topology BigOperators ComplexConjugate

local notation "E" => CoordinateSpace

section Rectangles

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private theorem iteratedIntegral_sum_compactRectangle {I J : Type*} [Fintype I] [Fintype J]
    (S T : Set X) (hS : IsCompact S) (hT : IsCompact T)
    (g : I → J → X × X → ℂ) (hg : ∀ i j, ContinuousOn (g i j) (S ×ˢ T)) :
    (∫ p in S, ∫ q in T, ∑ i, ∑ j, g i j (p, q) ∂μ ∂μ) =
      ∑ i, ∑ j, ∫ p in S, ∫ q in T, g i j (p, q) ∂μ ∂μ := by
  have hInt (i : I) (j : J) : Integrable (g i j) ((μ.restrict S).prod (μ.restrict T)) := by
    rw [Measure.prod_restrict]
    exact (hg i j).integrableOn_compact (hS.prod hT)
  have hInt' (i : I) : Integrable (fun z => ∑ j, g i j z) ((μ.restrict S).prod (μ.restrict T)) :=
    integrable_finset_sum Finset.univ fun j _ => hInt i j
  have hAll : Integrable (fun z => ∑ i, ∑ j, g i j z) ((μ.restrict S).prod (μ.restrict T)) :=
    integrable_finset_sum Finset.univ fun i _ => hInt' i
  rw [← integral_prod _ hAll, integral_finset_sum Finset.univ (fun i _ => hInt' i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => hInt i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_prod (g i j) (hInt i j)

end Rectangles

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M] in
theorem continuousOn_symmetricJetComponent (c : AtlasChart M) (s : SymmetricJetSection M)
    (hs : IsSmoothSymmetricJetSection s) (i : JetSlot) :
    ContinuousOn (symmetricJetComponent c s i) c.chart.source := by
  refine ((hs c i).continuousOn.comp c.chart.continuousOn c.chart.mapsTo).congr ?_
  intro p hp
  rw [Function.comp_apply, c.chart.left_inv hp]

omit [T2Space M] [SecondCountableTopology M] [Nonempty M] in
theorem measurable_symmetricJetComponent (c : AtlasChart M) (s : SymmetricJetSection M)
    (hs : IsSmoothSymmetricJetSection s) (i : JetSlot) : Measurable (symmetricJetComponent c s i) := by
  have h := (continuousOn_symmetricJetComponent c s hs i).measurable_piecewise
    (g := fun _ : M => (0 : ℂ)) continuousOn_const
    c.chart.open_source.measurableSet
  have he : c.chart.source.piecewise (symmetricJetComponent c s i) (fun _ => 0) =
      symmetricJetComponent c s i := by
    funext p
    by_cases hp : p ∈ c.chart.source
    · rw [piecewise_eq_of_mem _ _ _ hp]
    · rw [piecewise_eq_of_notMem _ _ _ hp]
      unfold symmetricJetComponent
      rw [dif_neg hp]
  rwa [he] at h

omit [T2Space M] in
private theorem integral_geometricVolume_compactChartKernel
    (B : Field (M := M)) (hB : IsSmooth B) [SFinite (ManifoldVolume.geometricMeasure B)]
    (c d : AtlasChart M) (S T : Set M) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSc : S ⊆ c.chart.source) (hTd : T ⊆ d.chart.source)
    (k : M → M → ℂ) (hk : Measurable (uncurry k))
    (hSupp : ∀ p q, p ∉ S ∨ q ∉ T → k p q = 0)
    (v u : M → ℂ) (hv : Measurable v) (hu : Measurable u) :
    (∫ p in S, conj (v p) * (∫ q in T, k p q * u q ∂ManifoldVolume.geometricMeasure B)
      ∂ManifoldVolume.geometricMeasure B) =
      ∫ x, conj (receivingScalarTestHalfDensity B c v x) *
        (∫ y, receivingHalfDensityKernel B c d k x y * receivingScalarTestHalfDensity B d u y) := by
  let μ := ManifoldVolume.geometricMeasure B
  have hInput (p : M) : (∫ q in T, k p q * u q ∂μ) =
      ∫ q in d.chart.source, k p q * u q ∂μ := by
    rw [← integral_indicator hT, ← integral_indicator d.chart.open_source.measurableSet]
    apply integral_congr_ae
    filter_upwards with q
    by_cases hq : q ∈ T
    · rw [indicator_of_mem hq, indicator_of_mem (hTd hq)]
    · rw [indicator_of_notMem hq]
      by_cases hqd : q ∈ d.chart.source
      · rw [indicator_of_mem hqd, hSupp p q (Or.inr hq), zero_mul]
      · rw [indicator_of_notMem hqd]
  rw [show (∫ p in S, conj (v p) * (∫ q in T, k p q * u q ∂μ) ∂μ) =
      ∫ p in c.chart.source, conj (v p) * (∫ q in d.chart.source, k p q * u q ∂μ) ∂μ from by
        rw [← integral_indicator hS, ← integral_indicator c.chart.open_source.measurableSet]
        apply integral_congr_ae
        filter_upwards with p
        by_cases hp : p ∈ S
        · rw [indicator_of_mem hp, indicator_of_mem (hSc hp), hInput p]
        · rw [indicator_of_notMem hp]
          by_cases hpc : p ∈ c.chart.source
          · rw [indicator_of_mem hpc]
            simp_rw [hSupp p _ (Or.inl hp), zero_mul, integral_zero, mul_zero]
          · rw [indicator_of_notMem hpc]]
  rw [integral_geometricVolume_separatedChartKernel B hB c d k hk v u hv hu,
    ← integral_indicator c.chart.open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ c.chart.target
  · rw [indicator_of_mem hx, ← integral_indicator d.chart.open_target.measurableSet]
    change conj ((fixedHalfDensity B c x : ℂ) * v (c.chart.symm x)) * _ =
      conj (c.chart.target.indicator _ x) * _
    rw [indicator_of_mem hx]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ d.chart.target
    · rw [indicator_of_mem hy]
      unfold receivingScalarTestHalfDensity
      rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      unfold receivingScalarTestHalfDensity
      rw [indicator_of_notMem hy, mul_zero]
  · rw [indicator_of_notMem hx]
    unfold receivingScalarTestHalfDensity
    rw [indicator_of_notMem hx, map_zero, zero_mul]

/-- Restrict the ordered matrix entry to the actual output/input rectangle
before using it in the cross-chart integral. -/
def symmetricJetWindowKernelEntry (K : SymmetricJetPairingKernel M) (c d : AtlasChart M)
    (S T : Set M) (i j : JetSlot) (p q : M) : ℂ :=
  (S ×ˢ T).indicator (uncurry (symmetricJetKernelEntry K c d i j)) (p, q)

/-- An actual global bundle pairing reads as a finite sum of its own
separated half-density kernels in two genuine receiving charts. -/
theorem symmetricJetGlobalForm_eq_separatedChartPairings
    (B : Field (M := M)) (hB : IsSmooth B)
    (form : SymmetricJetGlobalForm M) (K : SymmetricJetPairingKernel M)
    (hForm : HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B) form K)
    (c d : AtlasChart M) (S T : Set M) (hS : IsCompact S) (hT : IsCompact T) (hST : Disjoint S T)
    (hSc : S ⊆ c.chart.source) (hTd : T ⊆ d.chart.source)
    (hK : ∀ i j, ContinuousOn (uncurry (symmetricJetKernelEntry K c d i j)) (S ×ˢ T))
    (v u : smoothCompactSymmetricJet M)
    (hvS : symmetricJetSectionSupport (v : SymmetricJetSection M) ⊆ S)
    (huT : symmetricJetSectionSupport (u : SymmetricJetSection M) ⊆ T) :
    form v u =
      ∑ i, ∑ j, ∫ x, conj (symmetricJetHalfDensity B c v.val i x) *
        (∫ y, receivingHalfDensityKernel B c d (symmetricJetWindowKernelEntry K c d S T i j) x y *
            symmetricJetHalfDensity B d u.val j y) := by
  let μ := ManifoldVolume.geometricMeasure B
  letI : IsLocallyFiniteMeasure μ := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  letI : SFinite (ManifoldVolume.geometricMeasure B) := by
    change SFinite μ
    infer_instance
  have hv : IsSmoothSymmetricJetSection v.val := v.property.1
  have hu : IsSmoothSymmetricJetSection u.val := u.property.1
  let k := symmetricJetWindowKernelEntry K c d S T
  let g (i j : JetSlot) (z : M × M) := conj (symmetricJetComponent c v.val i z.1) *
    (k i j z.1 z.2 * symmetricJetComponent d u.val j z.2)
  have hk (i j : JetSlot) : Measurable (uncurry (k i j)) := by
    have h := (hK i j).measurable_piecewise (g := fun _ : M × M => (0 : ℂ))
      continuousOn_const (hS.measurableSet.prod hT.measurableSet)
    have he : uncurry (k i j) = (S ×ˢ T).indicator (uncurry (symmetricJetKernelEntry K c d i j)) := by
      funext z
      rcases z with ⟨p, q⟩
      rfl
    have he' : (S ×ˢ T).indicator (uncurry (symmetricJetKernelEntry K c d i j)) =
        (S ×ˢ T).piecewise (uncurry (symmetricJetKernelEntry K c d i j)) (fun _ => 0) := by
      funext z
      by_cases hz : z ∈ S ×ˢ T
      · rw [indicator_of_mem hz, piecewise_eq_of_mem _ _ _ hz]
      · rw [indicator_of_notMem hz, piecewise_eq_of_notMem _ _ _ hz]
    rwa [he, he']
  have hkc (i j : JetSlot) : ContinuousOn (uncurry (k i j)) (S ×ˢ T) := by
    refine (hK i j).congr ?_
    intro z hz
    exact indicator_of_mem hz _
  have hg (i j : JetSlot) : ContinuousOn (g i j) (S ×ˢ T) := by
    have hp : MapsTo (Prod.fst : M × M → M) (S ×ˢ T) c.chart.source := fun _ hz => hSc hz.1
    have hq : MapsTo (Prod.snd : M × M → M) (S ×ˢ T) d.chart.source := fun _ hz => hTd hz.2
    have hc := (continuousOn_symmetricJetComponent c v.val hv i).comp continuous_fst.continuousOn
      hp
    have hd := (continuousOn_symmetricJetComponent d u.val hu j).comp continuous_snd.continuousOn
      hq
    exact (Complex.continuous_conj.comp_continuousOn hc).mul ((hkc i j).mul hd)
  rw [hForm S T hS hT hST v u hvS huT]
  calc
    _ = ∫ p in S, ∫ q in T, ∑ i, ∑ j, g i j (p, q) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := μ) hS.measurableSet] with p hp
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := μ) hT.measurableSet] with q hq
      rw [symmetricJetPairingKernel_eq_sum_entries K c d v.val u.val p q (hSc hp) (hTd hq)]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hh : k i j p q = symmetricJetKernelEntry K c d i j p q := by
        change (S ×ˢ T).indicator (uncurry (symmetricJetKernelEntry K c d i j)) (p, q) = _
        rw [indicator_of_mem (show (p, q) ∈ S ×ˢ T from ⟨hp, hq⟩)]
        rfl
      simp only [g, hh, mul_assoc]
    _ = ∑ i, ∑ j, ∫ p in S, ∫ q in T, g i j (p, q) ∂μ ∂μ :=
      iteratedIntegral_sum_compactRectangle μ S T hS hT g hg
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [g, integral_const_mul]
      exact integral_geometricVolume_compactChartKernel B hB c d S T hS.measurableSet hT.measurableSet
        hSc hTd (k i j) (hk i j)
        (fun p q h => indicator_of_notMem (show (p, q) ∉ S ×ˢ T from not_and_or.mpr h) _)
        (symmetricJetComponent c v.val i) (symmetricJetComponent d u.val j)
        (measurable_symmetricJetComponent c v.val hv i) (measurable_symmetricJetComponent d u.val hu j)

end Burnett.Microlocal.Overlap
