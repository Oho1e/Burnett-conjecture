import Burnett.Analysis.Microlocal.Overlap.TransportedGradientL2
import Burnett.Analysis.Microlocal.Overlap.CovariantGradientTransition
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-!
# Transported covariant gradients as finite sums in the target chart

The forward and reverse half-density weights cancel on a true overlap. The
three tensor slots then contribute the actual Jacobian product, evaluated at
the inverse transition of the target coordinate. A single compact cutoff
extends these smooth coefficient functions to legitimate whole-space multipliers.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovariantGradient

open Filter MeasureTheory Set
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.X02.SobolevTestJet (D)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open scoped BigOperators ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Three covariant indices contribute the product of forward Jacobian entries
at the source point corresponding to a target coordinate. -/
def overlapJetCoefficient (c d : M) (i j : JetSlot) (y : CoordinateSpace) : ℝ :=
  let J := derivativeMatrix (fderiv ℝ (chartTransition c d) (overlapTransition d c y))
  J j.1 i.1 * J j.2.1 i.2.1 * J j.2.2 i.2.2

theorem overlapJetCoefficient_smoothOn (c d : M) (i j : JetSlot) :
    ContDiffOn ℝ ∞ (overlapJetCoefficient c d i j) (chartTransition c d).target := by
  let e := chartTransition c d
  have hSymm : e.symm = chartTransition d c := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hTarget : e.target = (chartTransition d c).source := by
    change e.symm.source = _
    rw [hSymm]
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (ActualChartSecondJet.contDiffOn_chartTransition_infty c d).fderiv_of_isOpen e.open_source (by simp)
  have hJ (a b : Index) : ContDiffOn ℝ ∞
      (fun x => derivativeMatrix (fderiv ℝ e x) a b) e.source := by
    simpa only [derivativeMatrix_apply] using
      (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp_contDiffOn
        (hD.clm_apply (contDiffOn_const :
          ContDiffOn ℝ ∞ (fun _ : CoordinateSpace => coordinateBasis b) e.source))
  have hReverse : MapsTo (overlapTransition d c) e.target e.source := by
    intro y hy
    rw [overlapTransition_eq d c (hTarget ▸ hy), ← hSymm]
    exact e.symm_mapsTo hy
  have hSmooth : ContDiffOn ℝ ∞ (overlapTransition d c) e.target :=
    hTarget.symm ▸ overlapTransition_contDiffOn d c
  exact (((hJ j.1 i.1).mul (hJ j.2.1 i.2.1)).mul (hJ j.2.2 i.2.2)).comp hSmooth hReverse

/-- One compact target cutoff suffices for all the coefficient multipliers. -/
theorem exists_overlapJetCoefficient_tests (c d : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source) :
    ∃ θ : D, ∃ w : JetSlot → JetSlot → D,
      tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartTransition c d).target ∧
      (∀ y ∈ chartTransition c d '' K, (θ : CoordinateSpace → ℝ) y = 1) ∧
      (∀ i j, tsupport (w i j : CoordinateSpace → ℝ) ⊆ tsupport (θ : CoordinateSpace → ℝ)) ∧
      ∀ i j, EqOn (w i j : CoordinateSpace → ℝ) (overlapJetCoefficient c d i j)
        (chartTransition c d '' K) := by
  let e := chartTransition c d
  have hImage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hImageTarget : e '' K ⊆ e.target := image_subset_iff.mpr (e.mapsTo.mono_left hKU)
  obtain ⟨_, _, _, hL, θ, hθ, hθC, hθL, _, hθOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hImage e.open_target hImageTarget
  have hθTarget := hθL.trans hL
  let v : D := ⟨θ, hθ, hθC⟩
  let w (i j : JetSlot) : D :=
    ⟨fun y => θ y * overlapJetCoefficient c d i j y,
      contDiff_test_mul_local e.open_target hθ hθTarget (overlapJetCoefficient_smoothOn c d i j),
      hθC.mul_right⟩
  refine ⟨v, w, hθTarget, hθOne, fun i j => tsupport_mul_subset_left, ?_⟩
  intro i j y hy
  change θ y * overlapJetCoefficient c d i j y = overlapJetCoefficient c d i j y
  rw [hθOne y hy, one_mul]

/-- Exact whole-space identity after changing the chart of the genuine gradient. -/
theorem transportedCovariantGradientSchwartz_eq_sum (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ η : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K)
    (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target)
    (hηK : tsupport (η : CoordinateSpace → ℝ) ⊆ chartTransition c d '' K)
    (hCut : ∀ x ∈ (chartTransition c d).source,
      (η : CoordinateSpace → ℝ) (chartTransition c d x) = (χ : CoordinateSpace → ℝ) x)
    (w : JetSlot → JetSlot → D)
    (hw : ∀ i j, EqOn (w i j : CoordinateSpace → ℝ) (overlapJetCoefficient c d i j)
      (chartTransition c d '' K)) (n : ℕ) (i : JetSlot) (y : CoordinateSpace) :
    transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i y =
      ∑ j : JetSlot, ((w i j : CoordinateSpace → ℝ) y : ℂ) *
        originalCovariantGradientSchwartz r B g hB hg hn d η hη n j y := by
  let e := chartTransition c d
  let hc := (hχ.trans hKU).trans (overlapSource_subset_chartTarget c d)
  let f := originalCovariantGradientSchwartz r B g hB hg hn c χ hc n i
  change transportedHalfDensity c d K f y = _
  by_cases hy : y ∈ e '' K
  · obtain ⟨x, hx, rfl⟩ := hy
    have hSource := hKU hx
    have hBack : overlapTransition d c (e x) = x := overlapTransition_reverse_apply c d hSource
    rw [transportedHalfDensity, indicator_of_mem (mem_image_of_mem e hx), hBack]
    change overlapJacobianWeight d c (e x) •
      originalCovariantGradientSchwartz r B g hB hg hn c χ hc n i x = _
    rw [originalCovariantGradientSchwartz_overlap r B g hB hg hn c d χ η hc hη hCut n hSource i]
    have hWeight : (overlapJacobianWeight d c (e x) : ℂ) * (overlapJacobianWeight c d x : ℂ) = 1 := by
      exact_mod_cast (mul_comm _ _).trans (overlapJacobianWeight_inverse_mul c d hSource)
    rw [overlapJetPullback, Complex.real_smul, ← mul_assoc, hWeight, one_mul]
    simp only [Fintype.sum_prod_type, hw _ _ (mem_image_of_mem e hx), overlapJetCoefficient, hBack]
    rfl
  · rw [transportedHalfDensity, indicator_of_notMem hy]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hz : originalCovariantGradientSchwartz r B g hB hg hn d η hη n j y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy
        (hηK (originalCovariantGradientSchwartz_tsupport r B g hB hg hn d η hη n j h)))
    rw [hz, mul_zero]

/-- The actual localized sequence supplies the common cutoff, the smooth compact
multipliers, the pointwise jet formula, and both strongly vanishing errors. -/
theorem exists_originalGradient_overlap_transport (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K) :
    ∃ η : D, ∃ hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target,
    ∃ θ : D, ∃ w : JetSlot → JetSlot → D,
      tsupport (η : CoordinateSpace → ℝ) ⊆ chartTransition c d '' tsupport (χ : CoordinateSpace → ℝ) ∧
      (∀ x ∈ (chartTransition c d).source,
        (η : CoordinateSpace → ℝ) (chartTransition c d x) = (χ : CoordinateSpace → ℝ) x) ∧
      tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartTransition c d).target ∧
      (∀ y ∈ chartTransition c d '' K, (θ : CoordinateSpace → ℝ) y = 1) ∧
      (∀ i j, tsupport (w i j : CoordinateSpace → ℝ) ⊆ tsupport (θ : CoordinateSpace → ℝ)) ∧
      (∀ i j, EqOn (w i j : CoordinateSpace → ℝ) (overlapJetCoefficient c d i j)
        (chartTransition c d '' K)) ∧
      (∀ n i y,
        transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i y =
          ∑ j : JetSlot, ((w i j : CoordinateSpace → ℝ) y : ℂ) *
            originalCovariantGradientSchwartz r B g hB hg hn d η hη n j y) ∧
      (∀ i, Tendsto (fun n =>
        (transportedOriginalVolumeGradientSchwartz B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume -
        (transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume)
        atTop (𝓝 0)) ∧
      (∀ i, Tendsto (fun n => originalGradient_volumeWeightedL2 B g hB hg hn d η hη n i -
        originalCovariantGradientL2 r B g hB hg hn d η hη n i) atTop (𝓝 0)) := by
  obtain ⟨η, hηS, hCut⟩ := exists_transportOverlapCutoff c d χ (hχ.trans hKU)
  have hηK := hηS.trans (image_mono hχ)
  have hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target := by
    apply hηK.trans
    rintro y ⟨x, hx, rfl⟩
    exact ((chartTransition c d).mapsTo (hKU hx)).1
  obtain ⟨θ, w, hθ, hOne, hSupport, hw⟩ := exists_overlapJetCoefficient_tests c d K hK hKU
  exact ⟨η, hη, θ, w, hηS, hCut, hθ, hOne, hSupport, hw,
    transportedCovariantGradientSchwartz_eq_sum r B g hB hg hn c d K hK hKU χ η hχ hη hηK hCut w hw,
    transportedOriginalVolumeGradient_sub_covariant_tendsto_zero r B g hB hg hn hconv c d K hK hKU χ hχ,
    originalGradient_sub_covariantGradient_tendsto_zero r B g hB hg hn hconv d η hη⟩

end Burnett.F05.OverlapCovariantGradient
