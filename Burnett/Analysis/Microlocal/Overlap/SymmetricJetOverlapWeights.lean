import Burnett.Analysis.Microlocal.Overlap.SymmetricJetChartLiftChange
import Burnett.Analysis.Microlocal.Overlap.CompactSymmetricJetWindowData
import Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing

/-! Actual three-slot chart changes are smooth weights on compact windows. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Matrix Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart ChartVolume
open Burnett.RicciSymbol (Index)
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F05.OverlapCovectors (tensorJetTransition tensorPairTransition)
open Burnett.Microlocal.AtlasOverlapKernel
open scoped BigOperators ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

private theorem rawReceivingJetTransition_single_contDiffOn (c d : AtlasChart M)
    (i j : JetSlot) :
    ContDiffOn ℝ ∞ (fun x => rawReceivingJetTransition c d x (Pi.single j 1) i) (c.transition d).source := by
  let e := c.transition d
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp)
  have hDEntry (a b : Index) :
      ContDiffOn ℝ ∞ (fun x => (derivativeMatrix (fderiv ℝ e x) a b : ℂ)) e.source := by
    simp only [derivativeMatrix_apply]
    exact (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff).comp_contDiffOn
      (hD.clm_apply contDiffOn_const)
  simp only [rawReceivingJetTransition, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    tensorJetTransition, tensorPairTransition]
  exact (hDEntry j.1 i.1).mul ((hDEntry j.2.1 i.2.1).mul (hDEntry j.2.2 i.2.2))

/-- From c-components to d-components at the same actual point, expressed
as a smooth weight in the source variables on the overlap. -/
def receivingJetOverlapWeight (c d : AtlasChart M) (i j : JetSlot) (x : E) : ℂ :=
  rawReceivingJetTransition d c (c.transition d x) (Pi.single j 1) i

theorem receivingJetOverlapWeight_contDiffOn (c d : AtlasChart M) (i j : JetSlot) :
    ContDiffOn ℝ ∞ (receivingJetOverlapWeight c d i j) (c.transition d).source := by
  have hMap : MapsTo (c.transition d) (c.transition d).source (d.transition c).source := by
    have hRev : (c.transition d).symm = d.transition c := by
      simp only [AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [← hRev]
    exact (c.transition d).mapsTo
  exact (rawReceivingJetTransition_single_contDiffOn d c i j).comp (c.smooth_transition d) hMap

/-- Extend the actual transition as smooth scalar weights without changing
any coefficient on the given compact overlap. -/
theorem exists_smoothReceivingJetOverlapWeights (c d : AtlasChart M)
    (K : Set E) (hK : IsCompact K) (hKc : K ⊆ (c.transition d).source) :
    ∃ u : JetSlot → JetSlot → E → ℂ, (∀ i j, ContDiff ℝ ∞ (u i j)) ∧
      ∀ i j x, x ∈ K → u i j x = receivingJetOverlapWeight c d i j x := by
  obtain ⟨J, _, _, hJU, q, hq, _, hqS, _, hqK⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK (c.transition d).open_source hKc
  let q' (x : E) := (q x : ℂ)
  have hq' : ContDiff ℝ ∞ q' := Complex.ofRealCLM.contDiff.comp hq
  have hq'U : tsupport q' ⊆ (c.transition d).source := by
    apply (closure_mono (show support q' ⊆ support q from fun x hx h => hx (by simp [q', h]))).trans
    exact hqS.trans hJU
  refine ⟨fun i j x => q' x * receivingJetOverlapWeight c d i j x, fun i j => ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ (c.transition d).source
    · exact hq'.contDiffAt.mul ((receivingJetOverlapWeight_contDiffOn c d i j).contDiffAt
        ((c.transition d).open_source.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hq'U h))] with y hy
      change q' y = 0 at hy
      simp only [hy, zero_mul]
  · intro i j x hx
    simp only [q', hqK x hx, Complex.ofReal_one, one_mul]

variable [T2Space M] [SecondCountableTopology M] [IsManifold Model ∞ M]

open private compactWeightedSchwartz_tsupport from Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing

/-- The actual supported c-chart singleton becomes a d-chart array: each
entry is the scalar half-density transport of one weighted c-chart profile. -/
theorem supportedSymmetricJetChartTest_single_eq_transport
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (c d : AtlasChart M)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (hKc : K ⊆ c.chart.target) (hKd : (c.transition d '' K) ⊆ d.chart.target)
    (hK' : IsCompact ((c.transition d) '' K))
    (u : JetSlot → JetSlot → E → ℂ) (hu : ∀ i j, ContDiff ℝ ∞ (u i j))
    (hU : ∀ i j x, x ∈ K → u i j x = receivingJetOverlapWeight c d i j x)
    (i : JetSlot) (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ))
    (hfK : tsupport (f : E → ℂ) ⊆ K) :
    let g (j : JetSlot) := compactWeightedSchwartz (u j i) (hu j i) f hf
    let hg (j : JetSlot) : tsupport (g j : E → ℂ) ⊆ K := (compactWeightedSchwartz_tsupport _ _ _ _).trans hfK
    let w (j : JetSlot) := transportedHalfDensitySchwartz c d K hK hKU (g j) (hg j)
    let hw (j : JetSlot) : tsupport (w j : E → ℂ) ⊆ c.transition d '' K :=
      (transportedHalfDensity_smooth_compact_support c d K hK hKU (g j) (hg j)).2.2
    supportedSymmetricJetChartTest B hB hn c K hK hKc (Pi.single i f) (tsupport_singleSymmetricJetWindow_subset i f hfK) =
      supportedSymmetricJetChartTest B hB hn d (c.transition d '' K) hK' hKd w hw := by
  intro g hg w hw
  apply Subtype.ext
  apply symmetricJetChartLift_eq_of_transport B hn c d K hKU
  · intro j
    exact (subset_tsupport _).trans (tsupport_singleSymmetricJetWindow_subset i f hfK j)
  · intro j
    exact (subset_tsupport _).trans (hw j)
  · intro x hx y
    have hS := hKU hx
    have hy : y ∈ (c.transition d '' K) := mem_image_of_mem _ hx
    have hReverse : overlapTransition d c y = x := overlapTransition_reverse_apply c d hS
    have hEval : (fun j => ((Pi.single i f : JetSlot → SchwartzMap E ℂ) j) x) =
        (f x) • (Pi.single i 1 : JetSlot → ℂ) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]
      · simp only [Pi.single_eq_of_ne hj, SchwartzMap.zero_apply, Pi.smul_apply, smul_eq_mul, mul_zero]
    funext j
    have hLeft : (w j : E → ℂ) = transportedHalfDensity c d K (g j) :=
      coe_transportedHalfDensitySchwartz c d K hK hKU (g j) (hg j)
    simp only [hLeft, transportedHalfDensity, indicator_of_mem hy, hReverse,
      g, compactWeightedSchwartz_apply, hU j i x hx, receivingJetOverlapWeight, hEval, map_smul,
      Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring

end Burnett.Microlocal.Overlap
