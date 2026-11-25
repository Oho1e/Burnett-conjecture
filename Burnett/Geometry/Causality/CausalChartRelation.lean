import Burnett.Geometry.Causality.ChartCausalFuture
import Burnett.Geometry.Causality.CausalVolumeAssembly

set_option autoImplicit false
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A continuously differentiable future causal segment in a chart box, described with a fixed
future timelike reference vector and the actual metric. -/
def HasFutureCausalChartSegment {g : Field (M := M)} (o : TimeOrientation g) (p q : M) : Prop :=
  ∃ (c : M) (x n : E) (r R a b V : ℝ) (γ v : ℝ → E),
    p = (chartAt E c).symm (γ a) ∧ q = (chartAt E c).symm (γ b) ∧ a < b ∧ r < R ∧ 0 ≤ V ∧
    Metric.closedBall x R ⊆ (chartAt E c).target ∧
    (∀ z ∈ Metric.closedBall x R, coordinateBilinear g c z n n < 0) ∧
    (∀ z ∈ Metric.closedBall x R, coordinateBilinear g c z n (ChartVectorField.coordinateVector o.vector c z) < 0) ∧
    ContDiffOn ℝ 1 γ (Icc a b) ∧
    ∀ t ∈ Icc a b, γ t ∈ Metric.closedBall x r ∧ HasDerivAt γ (v t) t ∧
      coordinateBilinear g c (γ t) (v t) (v t) ≤ 0 ∧ coordinateBilinear g c (γ t) n (v t) ≤ 0 ∧ ‖v t‖ ≤ V

/-- Causal connection is the reflexive transitive closure of the timelike
chords and the local future causal chart segments. -/
def chartCausalRelation {g : Field (M := M)} (o : TimeOrientation g) : Set (M × M) :=
  {z | Relation.ReflTransGen (fun p q => (p, q) ∈ chartChronology o ∨ HasFutureCausalChartSegment o p q) z.1 z.2}

theorem chartChronology_subset_chartCausalRelation {g : Field (M := M)} (o : TimeOrientation g) :
    chartChronology o ⊆ chartCausalRelation o :=
  fun _ h => Relation.ReflTransGen.single (Or.inl h)

theorem chartCausalRelation_transitive {g : Field (M := M)} (o : TimeOrientation g) :
    Transitive fun x y : M => (x, y) ∈ chartCausalRelation o :=
  fun _ _ _ h₁ h₂ => Relation.ReflTransGen.trans h₁ h₂

theorem chartCausalRelation_chronological_inclusions {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    {p q : M} (h : (p, q) ∈ chartCausalRelation o) :
    sectionAt (chartChronology o) p ⊆ sectionAt (chartChronology o) q ∧
    sectionAt (Prod.swap ⁻¹' chartChronology o) q ⊆ sectionAt (Prod.swap ⁻¹' chartChronology o) p := by
  change Relation.ReflTransGen (fun p q => (p, q) ∈ chartChronology o ∨ HasFutureCausalChartSegment o p q) p q at h
  induction h with
  | refl => exact ⟨Subset.rfl, Subset.rfl⟩
  | @tail b c _ hb ih =>
      rcases hb with h | h
      · have hF : sectionAt (Prod.swap ⁻¹' chartChronology o) c ⊆
            sectionAt (Prod.swap ⁻¹' chartChronology o) b :=
          fun _ hx => Relation.TransGen.trans h hx
        exact ⟨ih.1.trans (fun _ hx => Relation.TransGen.trans hx h), hF.trans ih.2⟩
      · obtain ⟨chart, x, n, r, R, a, d, V, γ, v, rfl, rfl, hab, hRad, hV, hTarget, hn, hnT, _, hPath⟩ := h
        exact ⟨ih.1.trans (chartCausalWindow_past_subset hg hL o chart x n hab hRad hTarget hn hnT γ v hV hPath),
          (chartCausalWindow_future_subset hg hL o chart x n hab hRad hTarget hn hnT γ v hV hPath).trans ih.2⟩

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem exists_continuous_strict_chartCausal_time {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g)
    (hNoLoop : ∀ p, (p, p) ∉ chartChronology o)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ chartCausalRelation o ∧ (z, b) ∈ chartCausalRelation o})
    (hLoc : ∀ x : M, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → (a, z) ∈ chartCausalRelation o → (z, b) ∈ chartCausalRelation o → z ∈ V) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
      ManifoldVolume.geometricMeasure g ≪ μ ∧ μ ≪ ManifoldVolume.geometricMeasure g ∧
      let T p := Real.log (μ (sectionAt (chartChronology o) p)).toReal -
        Real.log (μ (sectionAt (Prod.swap ⁻¹' chartChronology o) p)).toReal
      Continuous T ∧ ∀ ⦃a b : M⦄, (a, b) ∈ chartCausalRelation o → a ≠ b → T a < T b :=
  exists_continuous_strictCausal_volume_time hg hL o (chartChronology_subset_chartCausalRelation o)
    (chartCausalRelation_transitive o) hNoLoop hDiam hLoc
    (fun _ _ h => (chartCausalRelation_chronological_inclusions hg hL o h).1)
    (fun _ _ h => (chartCausalRelation_chronological_inclusions hg hL o h).2)

end Burnett.Geometry.FiniteCausalVolume
