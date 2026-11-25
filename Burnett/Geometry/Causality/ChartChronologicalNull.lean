import Burnett.Geometry.Causality.CausalVolumeContinuity
import Burnett.Geometry.ManifoldLorentzSignature
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A straight timelike segment in an actual chart, in either orientation. -/
def HasTimelikeChartChord (g : Field (M := M)) (a b : M) : Prop :=
  ∃ c : M, let e := chartAt CoordinateSpace c
    a ∈ e.source ∧ b ∈ e.source ∧
      ∀ t ∈ Icc (0 : ℝ) 1, let y := AffineMap.lineMap (e a) (e b) t
        y ∈ e.target ∧ coordinateBilinear g c y (e b - e a) (e b - e a) < 0

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Locally, a measurable set containing no timelike chord occupies at most
one time per spatial coordinate in a Lorentz frame. Its geometric volume is zero. -/
theorem exists_open_zero_volume_of_no_timelike_chart_chord (g : Field (M := M))
    (hg : IsSmooth g) (hL : HasLorentzSignature g) {A : Set M} (hA : MeasurableSet A)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, ¬ HasTimelikeChartChord g a b) (c : M) :
    ∃ W : Set M, IsOpen W ∧ c ∈ W ∧ ManifoldVolume.geometricMeasure g (A ∩ W) = 0 := by
  classical
  let e := chartAt CoordinateSpace c
  let y₀ := e c
  have hc : c ∈ e.source := mem_chart_source CoordinateSpace c
  have hy₀ : y₀ ∈ e.target := e.mapsTo hc
  let E := (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ c hc
  obtain ⟨b, hb⟩ := hL c
  let b' := b.map E.toLinearEquiv
  let v := b' (0 : Index)
  let B := coordinateBilinear g c
  have hv : B y₀ v v < 0 := by
    have hv' : tangentFrame c c v = b 0 := E.symm_apply_apply (b 0)
    change g (e.symm (e c)) (tangentFrame c (e.symm (e c)) v) (tangentFrame c (e.symm (e c)) v) < 0
    rw [e.left_inv hc, hv', hb]
    norm_num [TensorFrame.standardInverse, TensorFrame.signature]
  have hct : ContinuousAt (fun y => B y v v) y₀ :=
    (contDiffOn_coordinateBilinear_apply g hg c v v).continuousOn.continuousAt (e.open_target.mem_nhds hy₀)
  have hnb : e.target ∩ {y | B y v v < 0} ∈ 𝓝 y₀ :=
    Filter.inter_mem (e.open_target.mem_nhds hy₀) (hct.preimage_mem_nhds (Iio_mem_nhds hv))
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hnb
  let U := Metric.ball y₀ r
  have hUt : U ⊆ e.target := hBall.trans inter_subset_left
  let W := e.symm '' U
  have hW : IsOpen W := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hUt
  have hcW : c ∈ W := ⟨y₀, Metric.mem_ball_self hr, e.left_inv hc⟩
  have hWs : W ⊆ e.source := image_subset_iff.mpr (e.symm_mapsTo.mono_left hUt)
  let S := ManifoldVolume.inverseChart c ⁻¹' A ∩ U
  have hS : MeasurableSet S :=
    (hA.preimage (ManifoldVolume.measurable_inverseChart c)).inter Metric.isOpen_ball.measurableSet
  have hImg : e '' (A ∩ W) = S := by
    ext y
    constructor
    · rintro ⟨a, ⟨ha, z, hz, rfl⟩, rfl⟩
      rw [e.right_inv (hUt hz)]
      exact ⟨by simpa only [mem_preimage, ManifoldVolume.inverseChart_of_mem c (hUt hz)] using ha, hz⟩
    · rintro ⟨hyA, hyU⟩
      have hae : e.symm y ∈ A := by
        simpa only [mem_preimage, ManifoldVolume.inverseChart_of_mem c (hUt hyU)] using hyA
      exact ⟨e.symm y, ⟨hae, y, hyU, rfl⟩, e.right_inv (hUt hyU)⟩
  let L : CoordinateSpace ≃L[ℝ] (Index → ℝ) := b'.equivFun.toContinuousLinearEquiv
  let K₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Index => ℝ) (0 : Index)
  let K : (Index → ℝ) ≃ᵐ (Fin 3 → ℝ) × ℝ := K₀.trans (MeasurableEquiv.prodComm : ℝ × (Fin 3 → ℝ) ≃ᵐ _)
  let P := K '' (L '' S)
  have hP : MeasurableSet P := K.measurableEmbedding.measurableSet_image.mpr
    (L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS)
  have hAxis (w : Index → ℝ) (i : Fin 3) : (K w).1 i = w i.succ := by
    change w ((0 : Index).succAbove i) = w i.succ
    rw [Fin.succAbove_zero]
  have hAxisTime (w : Index → ℝ) : (K w).2 = w 0 := rfl
  have hline (z : Fin 3 → ℝ) : (Prod.mk z ⁻¹' P).Subsingleton := by
    rintro s ⟨_, ⟨a, ha, rfl⟩, hza⟩ t ⟨_, ⟨a', ha', rfl⟩, hza'⟩
    by_contra hst
    have hspace (i : Fin 3) : L a i.succ = L a' i.succ := by
      rw [← hAxis (L a) i, ← hAxis (L a') i, hza, hza']
    have htime : L a' 0 ≠ L a 0 := by
      rw [← hAxisTime (L a'), ← hAxisTime (L a), hza, hza']
      exact Ne.symm hst
    let d := L a' 0 - L a 0
    have hd : a' - a = d • v := by
      apply L.injective
      ext i
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hvL : L v i = if i = 0 then 1 else 0 := by
        change b'.equivFun (b' 0) i = _
        rw [Module.Basis.equivFun_self]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi, Ne.symm hi]
      rw [hvL]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [d]
      · simp [hspace j]
    have haA : e.symm a ∈ A := by
      simpa only [mem_preimage, ManifoldVolume.inverseChart_of_mem c (hUt ha.2)] using ha.1
    have ha'A : e.symm a' ∈ A := by
      simpa only [mem_preimage, ManifoldVolume.inverseChart_of_mem c (hUt ha'.2)] using ha'.1
    apply hNo _ haA _ ha'A
    refine ⟨c, e.symm_mapsTo (hUt ha.2), e.symm_mapsTo (hUt ha'.2), fun t ht => ?_⟩
    rw [e.right_inv (hUt ha.2), e.right_inv (hUt ha'.2)]
    have hy : AffineMap.lineMap a a' t ∈ U := by
      apply (convex_ball y₀ r).segment_subset ha.2 ha'.2
      rw [segment_eq_image_lineMap]
      exact mem_image_of_mem _ ht
    refine ⟨hUt hy, ?_⟩
    rw [hd]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact mul_neg_of_pos_of_neg (mul_self_pos.mpr (sub_ne_zero.mpr htime)) (hBall hy).2
  have hPzero : (volume : Measure ((Fin 3 → ℝ) × ℝ)) P = 0 :=
    measure_prod_zero_of_vertical_subsingleton volume volume hP hline
  have hK : MeasurePreserving K := (volume_preserving_piFinSuccAbove (fun _ : Index => ℝ) 0).trans
    (Measure.measurePreserving_swap : MeasurePreserving (Prod.swap : ℝ × (Fin 3 → ℝ) → _) _ _)
  have hLSzero : (volume : Measure (Index → ℝ)) (L '' S) = 0 := by
    rw [← K.preimage_image (L '' S), hK.measure_preimage hP.nullMeasurableSet]
    exact hPzero
  let μc := (volume : Measure CoordinateSpace).map L
  letI : μc.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  have hμc : μc ≪ (volume : Measure (Index → ℝ)) := Measure.absolutelyContinuous_isAddHaarMeasure μc volume
  have hSzero : (volume : Measure CoordinateSpace) S = 0 := by
    have hz := hμc hLSzero
    change (Measure.map L volume) (L '' S) = 0 at hz
    have hLS : MeasurableSet (L '' S) := L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS
    rw [Measure.map_apply L.continuous.measurable hLS,
      preimage_image_eq S L.injective] at hz
    exact hz
  refine ⟨W, hW, hcW, ?_⟩
  rw [ManifoldVolumeRegularity.geometricMeasure_apply_of_subset_chart g c
    (hA.inter hW.measurableSet) (inter_subset_right.trans hWs), hImg]
  exact withDensity_absolutelyContinuous _ _ hSzero

/-- All measurable sets with no timelike chart chord have zero geometric volume. -/
theorem geometricVolume_zero_of_no_timelike_chart_chord (g : Field (M := M))
    (hg : IsSmooth g) (hL : HasLorentzSignature g) {A : Set M} (hA : MeasurableSet A)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, ¬ HasTimelikeChartChord g a b) :
    ManifoldVolume.geometricMeasure g A = 0 := by
  classical
  choose W hW hcenter hzero using
    exists_open_zero_volume_of_no_timelike_chart_chord g hg hL hA hNo
  have hcover : (⋃ c, W c) = univ := eq_univ_of_forall fun c => mem_iUnion.mpr ⟨c, hcenter c⟩
  obtain ⟨T, hT, hsubcover⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hAcover : (⋃ c ∈ T, A ∩ W c) = A := by
    rw [← inter_iUnion₂, hsubcover, hcover, inter_univ]
  rw [← hAcover, measure_biUnion_null_iff hT]
  exact fun c _ => hzero c

end Burnett.Geometry.FiniteCausalVolume
