import Burnett.Geometry.ManifoldLorentzVolume
import Burnett.Geometry.MeasureGluing
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Compactness.Lindelof

/-!
# A global absolute-determinant measure on a four-manifold

Every local piece is transported along the actual restricted chart measurable
 equivalence and its inverse. Compatibility is proved from one fiberwise
 bilinear field and the established genuine chart-transition Jacobian law.
The global measure is a countable disjointed sum. Its characterization on
 all preferred charts `chartAt CoordinateSpace c`, for every `c : M`, proves
 independence of the countable subcover and of the existence choice.

The measurable structure on M is its Borel structure. No global frame,
 nonempty-manifold assumption, finite mass, supplied global measure, matrix
 transformation hypothesis, or final chart formula is an input. The empty
 manifold is handled separately. Values of inverseChart outside its target
 are an explicit measurable total-function convention and carry no smooth
 or geometric assertion.

This file treats the preferred chartAt family, not arbitrary maximal-atlas
 chart objects. It does not assert intrinsic Levi-Civita naturality, local
 finiteness/Radon properties, or an identification of a global Lorentz
 sequence and its derivative hypotheses.
-/

noncomputable section
namespace Burnett.Geometry.ManifoldVolume
open MeasureTheory Set Filter Classical
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ChartVolume

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- The measurable equivalence of the actual restricted chart. -/
def chartEquiv (c : M) : (chartAt CoordinateSpace c).source ≃ᵐ
    (chartAt CoordinateSpace c).target :=
  (chartAt CoordinateSpace c).toHomeomorphSourceTarget.toMeasurableEquiv

/-- A measurable total inverse, agreeing with the actual chart inverse on its target. -/
def inverseChart (c : M) (y : CoordinateSpace) : M :=
  ((chartAt CoordinateSpace c).target).piecewise (chartAt CoordinateSpace c).symm (fun _ => c) y

theorem measurable_inverseChart (c : M) : Measurable (inverseChart c) := by
  exact (chartAt CoordinateSpace c).continuousOn_symm.measurable_piecewise
    continuousOn_const (chartAt CoordinateSpace c).open_target.measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem inverseChart_of_mem (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    inverseChart c y = (chartAt CoordinateSpace c).symm y := by
  simp only [inverseChart, piecewise_eq_of_mem _ _ _ hy]

theorem inverseChart_eq_chartEquiv_symm (c : M) (y : (chartAt CoordinateSpace c).target) :
    inverseChart c y = ((chartEquiv c).symm y : M) := by
  exact inverseChart_of_mem c y.property

/-- Actual transport from one coordinate domain to the manifold. -/
def transport (c : M) (μ : Measure CoordinateSpace) : Measure M :=
  Measure.map (inverseChart c) (μ.restrict (chartAt CoordinateSpace c).target)

theorem transport_restrict (c : M) (μ : Measure CoordinateSpace) (V : Set M)
    (hV : MeasurableSet V) :
    (transport c μ).restrict V = Measure.map (inverseChart c)
      (μ.restrict ((chartAt CoordinateSpace c).target ∩ (chartAt CoordinateSpace c).symm ⁻¹' V)) := by
  rw [transport, Measure.restrict_map (measurable_inverseChart c) hV,
    Measure.restrict_restrict ((measurable_inverseChart c) hV)]
  congr 2
  ext y
  by_cases hy : y ∈ (chartAt CoordinateSpace c).target <;>
    simp [inverseChart, hy, and_comm]

theorem transport_restrict_source (c : M) (μ : Measure CoordinateSpace) :
    (transport c μ).restrict (chartAt CoordinateSpace c).source = transport c μ := by
  rw [transport_restrict c μ _ (chartAt CoordinateSpace c).open_source.measurableSet]
  have heq : (chartAt CoordinateSpace c).target ∩
      (chartAt CoordinateSpace c).symm ⁻¹' (chartAt CoordinateSpace c).source =
      (chartAt CoordinateSpace c).target :=
    inter_eq_left.mpr (chartAt CoordinateSpace c).symm_mapsTo
  rw [heq]
  rfl

theorem transport_restrict_overlap (c d : M) (μ : Measure CoordinateSpace) :
    (transport c μ).restrict ((chartAt CoordinateSpace c).source ∩ (chartAt CoordinateSpace d).source) =
      Measure.map (inverseChart c) (μ.restrict (chartTransition c d).source) := by
  rw [transport_restrict c μ _ ((chartAt CoordinateSpace c).open_source.measurableSet.inter
    (chartAt CoordinateSpace d).open_source.measurableSet)]
  congr 2
  ext y
  change (y ∈ (chartAt CoordinateSpace c).target ∧
    (chartAt CoordinateSpace c).symm y ∈ (chartAt CoordinateSpace c).source ∩
      (chartAt CoordinateSpace d).source) ↔
    (y ∈ (chartAt CoordinateSpace c).target ∧
      (chartAt CoordinateSpace c).symm y ∈ (chartAt CoordinateSpace d).source)
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, (chartAt CoordinateSpace c).symm_mapsTo h.1, h.2⟩⟩

variable [IsManifold Model ∞ M]

def coordinateMeasure
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c : M) : Measure CoordinateSpace :=
  LorentzVolume.coordinateMeasure (metricComponents (coordinateBilinear B c))

def localMeasure
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c : M) : Measure M := transport c (coordinateMeasure B c)

theorem localMeasure_compatible
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c d : M) :
    (localMeasure B c).restrict ((chartAt CoordinateSpace c).source ∩ (chartAt CoordinateSpace d).source) =
      (localMeasure B d).restrict ((chartAt CoordinateSpace c).source ∩ (chartAt CoordinateSpace d).source) := by
  let e := chartTransition c d
  have hmap : Measure.map e ((coordinateMeasure B c).restrict e.source) =
      (coordinateMeasure B d).restrict e.target :=
    ManifoldLorentzVolume.coordinateBilinear_geometric_measure_change B c d
  have heae : AEMeasurable e ((coordinateMeasure B c).restrict e.source) :=
    (contDiffOn_chartTransition c d).continuousOn.aemeasurable e.open_source.measurableSet
  calc
    _ = Measure.map (inverseChart c) ((coordinateMeasure B c).restrict e.source) :=
      transport_restrict_overlap c d _
    _ = Measure.map (inverseChart d) ((coordinateMeasure B d).restrict e.target) := by
      rw [← hmap, AEMeasurable.map_map_of_aemeasurable (measurable_inverseChart d).aemeasurable heae]
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with y hy
      simp only [Function.comp_apply, inverseChart_of_mem c hy.1,
        inverseChart_of_mem d (e.mapsTo hy).1]
      exact (chartTransition_symm_point c d hy).symm
    _ = _ := by
      change _ = (transport d (coordinateMeasure B d)).restrict _
      rw [inter_comm (chartAt CoordinateSpace c).source (chartAt CoordinateSpace d).source,
        transport_restrict_overlap d c]
      rfl


omit [MeasurableSpace M] [BorelSpace M] [IsManifold Model ∞ M] in
theorem inverseChart_chart (c : M) {x : M}
    (hx : x ∈ (chartAt CoordinateSpace c).source) :
    inverseChart c (chartAt CoordinateSpace c x) = x := by
  rw [inverseChart_of_mem c ((chartAt CoordinateSpace c).mapsTo hx),
    (chartAt CoordinateSpace c).left_inv hx]

omit [IsManifold Model ∞ M] in
theorem map_chart_transport (c : M) (μ : Measure CoordinateSpace) :
    Measure.map (chartAt CoordinateSpace c) (transport c μ) =
      μ.restrict (chartAt CoordinateSpace c).target := by
  have hc : AEMeasurable (chartAt CoordinateSpace c) (transport c μ) := by
    have hh := (chartAt CoordinateSpace c).continuousOn.aemeasurable
      (μ := transport c μ) (chartAt CoordinateSpace c).open_source.measurableSet
    rwa [transport_restrict_source] at hh
  unfold transport
  rw [AEMeasurable.map_map_of_aemeasurable hc (measurable_inverseChart c).aemeasurable]
  trans Measure.map id (μ.restrict (chartAt CoordinateSpace c).target)
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem (chartAt CoordinateSpace c).open_target.measurableSet] with y hy
    simp only [Function.comp_apply, inverseChart_of_mem c hy, id_eq]
    exact (chartAt CoordinateSpace c).right_inv hy
  · exact Measure.map_id

omit [IsManifold Model ∞ M] in
theorem map_inverse_chart_restrict (c : M) (μ : Measure M) :
    Measure.map (inverseChart c) (Measure.map (chartAt CoordinateSpace c)
      (μ.restrict (chartAt CoordinateSpace c).source)) =
      μ.restrict (chartAt CoordinateSpace c).source := by
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_inverseChart c).aemeasurable
    ((chartAt CoordinateSpace c).continuousOn.aemeasurable
      (chartAt CoordinateSpace c).open_source.measurableSet)]
  trans Measure.map id (μ.restrict (chartAt CoordinateSpace c).source)
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem (chartAt CoordinateSpace c).open_source.measurableSet] with x hx
    exact inverseChart_chart c hx
  · exact Measure.map_id

variable [SecondCountableTopology M]

omit [MeasurableSpace M] [BorelSpace M] [IsManifold Model ∞ M] in
theorem exists_countable_chart_cover [Nonempty M] :
    ∃ a : ℕ → M, ⋃ n, (chartAt CoordinateSpace (a n)).source = univ := by
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover
    (fun c : M => (chartAt CoordinateSpace c).source)
    (fun c => (chartAt CoordinateSpace c).open_source)
    (show (univ : Set M) ⊆ ⋃ c : M, (chartAt CoordinateSpace c).source from
      fun x hx => mem_iUnion.mpr ⟨x, mem_chart_source CoordinateSpace x⟩)
  exact ⟨a, eq_univ_of_univ_subset ha⟩

theorem exists_measure_restrict_local
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) :
    ∃ μ : Measure M, ∀ c : M,
      μ.restrict (chartAt CoordinateSpace c).source = localMeasure B c := by
  by_cases hne : Nonempty M
  · letI := hne
    obtain ⟨a, ha⟩ := exists_countable_chart_cover (M := M)
    let U := fun n => (chartAt CoordinateSpace (a n)).source
    let ν := fun n => localMeasure B (a n)
    refine ⟨MeasureGluing.glued U ν, fun c => ?_⟩
    have hg := MeasureGluing.glued_restrict_of_compatible U
      (fun n => (chartAt CoordinateSpace (a n)).open_source.measurableSet) ha ν
      (chartAt CoordinateSpace c).source (chartAt CoordinateSpace c).open_source.measurableSet
      (localMeasure B c) (fun n => localMeasure_compatible B (a n) c)
    exact hg.trans (transport_restrict_source c (coordinateMeasure B c))
  · haveI : IsEmpty M := not_nonempty_iff.mp hne
    exact ⟨0, fun c => isEmptyElim c⟩


omit [IsManifold Model ∞ M] [BorelSpace M] in
theorem measures_eq_of_chart_restrict (μ ν : Measure M)
    (h : ∀ c : M, μ.restrict (chartAt CoordinateSpace c).source =
      ν.restrict (chartAt CoordinateSpace c).source) : μ = ν := by
  by_cases hne : Nonempty M
  · letI := hne
    obtain ⟨a, ha⟩ := exists_countable_chart_cover (M := M)
    exact Measure.ext_of_iUnion_eq_univ ha (fun n => h (a n))
  · haveI : IsEmpty M := not_nonempty_iff.mp hne
    ext s hs
    have hs0 : s = ∅ := by ext x; exact isEmptyElim x
    simp only [hs0, measure_empty]

theorem existsUnique_measure_restrict_local
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) :
    ∃! μ : Measure M, ∀ c : M,
      μ.restrict (chartAt CoordinateSpace c).source = localMeasure B c := by
  obtain ⟨μ, hμ⟩ := exists_measure_restrict_local B
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  exact measures_eq_of_chart_restrict ν μ (fun c => (hν c).trans (hμ c).symm)

/-- The global measure is chosen from a proved existence theorem, whose
local pieces are the actual same-B coordinate densities. -/
def geometricMeasure
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) : Measure M :=
  (exists_measure_restrict_local B).choose

theorem geometricMeasure_restrict
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) (c : M) :
    (geometricMeasure B).restrict (chartAt CoordinateSpace c).source = localMeasure B c :=
  (exists_measure_restrict_local B).choose_spec c

/-- Every preferred chart, not only a chosen covering subfamily, has the
actual absolute-determinant coordinate measure as its pushforward. -/
theorem map_chart_geometricMeasure
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) (c : M) :
    Measure.map (chartAt CoordinateSpace c)
      ((geometricMeasure B).restrict (chartAt CoordinateSpace c).source) =
      (coordinateMeasure B c).restrict (chartAt CoordinateSpace c).target := by
  rw [geometricMeasure_restrict]
  exact map_chart_transport c (coordinateMeasure B c)

theorem eq_geometricMeasure_of_chart_formula
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (μ : Measure M)
    (hμ : ∀ c : M, Measure.map (chartAt CoordinateSpace c)
      (μ.restrict (chartAt CoordinateSpace c).source) =
      (coordinateMeasure B c).restrict (chartAt CoordinateSpace c).target) : μ = geometricMeasure B := by
  apply measures_eq_of_chart_restrict
  intro c
  rw [geometricMeasure_restrict]
  calc
    μ.restrict (chartAt CoordinateSpace c).source =
        Measure.map (inverseChart c) (Measure.map (chartAt CoordinateSpace c)
          (μ.restrict (chartAt CoordinateSpace c).source)) :=
      (map_inverse_chart_restrict c μ).symm
    _ = localMeasure B c := by rw [hμ c]; rfl

theorem existsUnique_measure_chart_formula
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ) :
    ∃! μ : Measure M, ∀ c : M, Measure.map (chartAt CoordinateSpace c)
      (μ.restrict (chartAt CoordinateSpace c).source) =
      (coordinateMeasure B c).restrict (chartAt CoordinateSpace c).target :=
  ⟨geometricMeasure B, map_chart_geometricMeasure B,
    fun μ hμ => eq_geometricMeasure_of_chart_formula B μ hμ⟩


/-- Any countable subcover of the preferred chartAt family gives exactly
the same global measure. No chosen covering sequence is a global input. -/
theorem glued_eq_geometricMeasure
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (a : ℕ → M) (ha : ⋃ n, (chartAt CoordinateSpace (a n)).source = univ) :
    MeasureGluing.glued (fun n => (chartAt CoordinateSpace (a n)).source)
      (fun n => localMeasure B (a n)) = geometricMeasure B := by
  apply Measure.ext_of_iUnion_eq_univ ha
  intro n
  calc
    _ = (localMeasure B (a n)).restrict (chartAt CoordinateSpace (a n)).source :=
      MeasureGluing.glued_restrict _
        (fun n => (chartAt CoordinateSpace (a n)).open_source.measurableSet) ha _
        (fun i j => localMeasure_compatible B (a i) (a j)) n
    _ = localMeasure B (a n) := transport_restrict_source _ _
    _ = _ := (geometricMeasure_restrict B (a n)).symm

theorem glued_cover_independent
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (a b : ℕ → M)
    (ha : ⋃ n, (chartAt CoordinateSpace (a n)).source = univ)
    (hb : ⋃ n, (chartAt CoordinateSpace (b n)).source = univ) :
    MeasureGluing.glued (fun n => (chartAt CoordinateSpace (a n)).source)
      (fun n => localMeasure B (a n)) =
    MeasureGluing.glued (fun n => (chartAt CoordinateSpace (b n)).source)
      (fun n => localMeasure B (b n)) :=
  (glued_eq_geometricMeasure B a ha).trans (glued_eq_geometricMeasure B b hb).symm

end Burnett.Geometry.ManifoldVolume
