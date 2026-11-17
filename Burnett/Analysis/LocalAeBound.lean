import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Local pointwise bounds from almost-everywhere bounds

The a.e. bound is taken on a larger set S containing an open neighborhood O
of the points under consideration. No positivity of the measure restricted
to a possibly null compact set K is assumed or inferred.
-/

noncomputable section

namespace Burnett.Analysis.LocalAeBound

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [NormedAddCommGroup F]

/-- A continuous scalar function cannot violate an a.e. upper bound at a
point of an open set on which every nonempty open subset has positive measure. -/
theorem le_on_open_of_ae_restrict_of_local_pos
    (μ : Measure X) {O S : Set X} (hO : IsOpen O) (hOS : O ⊆ S)
    (hpos : ∀ V : Set X, IsOpen V → V ⊆ O → V.Nonempty → μ V ≠ 0)
    {f : X → ℝ} (hf : ContinuousOn f O) {C : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, f x ≤ C) : ∀ x ∈ O, f x ≤ C := by
  have hae := ae_imp_of_ae_restrict (ae_restrict_of_ae_restrict_of_subset hOS hb)
  simp only [ae_iff, Classical.not_imp, not_le] at hae
  have hbad : IsOpen (O ∩ {x | C < f x}) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    exact inter_mem (hO.mem_nhds hx.1)
      ((hf.continuousAt (hO.mem_nhds hx.1)) (isOpen_Ioi.mem_nhds hx.2))
  intro x hx
  by_contra hle
  exact hpos _ hbad inter_subset_left ⟨x, hx, lt_of_not_ge hle⟩ hae

/-- The norm need only be continuous on the open neighborhood O. The bound
comes from the larger restricted measure on S, not from the measure on K. -/
theorem norm_le_on_of_ae_restrict_of_local_pos
    (μ : Measure X) {K O S : Set X} (hO : IsOpen O) (hKO : K ⊆ O) (hOS : O ⊆ S)
    (hpos : ∀ V : Set X, IsOpen V → V ⊆ O → V.Nonempty → μ V ≠ 0)
    {f : X → F} (hf : ContinuousOn (fun x => ‖f x‖) O) {C : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, ‖f x‖ ≤ C) : ∀ x ∈ K, ‖f x‖ ≤ C := by
  exact fun x hx =>
    le_on_open_of_ae_restrict_of_local_pos μ hO hOS hpos hf hb x (hKO hx)

/-- Specialization to a genuine measure positive on all nonempty opens. -/
theorem norm_le_on_of_ae_restrict
    (μ : Measure X) [μ.IsOpenPosMeasure] {K O S : Set X}
    (hO : IsOpen O) (hKO : K ⊆ O) (hOS : O ⊆ S)
    {f : X → F} (hf : ContinuousOn (fun x => ‖f x‖) O) {C : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, ‖f x‖ ≤ C) : ∀ x ∈ K, ‖f x‖ ≤ C := by
  exact norm_le_on_of_ae_restrict_of_local_pos μ hO hKO hOS
    (fun V hV _ hne => hV.measure_ne_zero μ hne) hf hb

omit [TopologicalSpace X] in
/-- A true extended L-infinity seminorm bound supplies the actual a.e.
norm bound; membership or a chosen representative is not silently assumed. -/
theorem ae_norm_le_of_eLpNorm_top_le {μ : Measure X} {f : X → F}
    {C : ℝ} (hC : 0 ≤ C) (hb : eLpNorm f ∞ μ ≤ ENNReal.ofReal C) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  rw [eLpNorm_exponent_top] at hb
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  simpa only [ofReal_norm] using hx.trans hb

/-- A restricted L-infinity bound on a neighborhood controls every point
of K, when the actual norm function is continuous on that neighborhood. -/
theorem norm_le_on_of_eLpNorm_top_le
    (μ : Measure X) [μ.IsOpenPosMeasure] {K O S : Set X}
    (hO : IsOpen O) (hKO : K ⊆ O) (hOS : O ⊆ S)
    {f : X → F} (hf : ContinuousOn (fun x => ‖f x‖) O)
    {C : ℝ} (hC : 0 ≤ C) (hb : eLpNorm f ∞ (μ.restrict S) ≤ ENNReal.ofReal C) :
    ∀ x ∈ K, ‖f x‖ ≤ C := by
  exact norm_le_on_of_ae_restrict μ hO hKO hOS hf
    (ae_norm_le_of_eLpNorm_top_le hC hb)

/-- The actual four-dimensional volume instance of the local bound. -/
theorem norm_le_on_of_eLpNorm_top_le_volume
    {K O S : Set (EuclideanSpace ℝ (Fin 4))}
    (hO : IsOpen O) (hKO : K ⊆ O) (hOS : O ⊆ S)
    {f : EuclideanSpace ℝ (Fin 4) → F} (hf : ContinuousOn (fun x => ‖f x‖) O)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : eLpNorm f ∞ (volume.restrict S) ≤ ENNReal.ofReal C) :
    ∀ x ∈ K, ‖f x‖ ≤ C := by
  exact norm_le_on_of_eLpNorm_top_le volume hO hKO hOS hf hC hb

/-- A continuous norm on a measurable set is a.e. strongly measurable for
the restricted measure. An actual a.e. bound then gives MemLp at every
exponent when that restricted measure is finite. -/
theorem norm_memLp_restrict_of_continuousOn_of_ae_bound [OpensMeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) (hfinite : μ S < ∞)
    {f : X → F} (hf : ContinuousOn (fun x => ‖f x‖) S) {C : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, ‖f x‖ ≤ C) (p : ℝ≥0∞) :
    MemLp (fun x => ‖f x‖) p (μ.restrict S) := by
  classical
  letI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfinite⟩
  let q : X → ℝ := S.piecewise (fun x => ‖f x‖) (fun _ => 0)
  have hq : Measurable q := hf.measurable_piecewise continuousOn_const hS
  have heq : q =ᵐ[μ.restrict S] (fun x => ‖f x‖) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simp only [q, Set.piecewise_eq_of_mem S _ _ hx]
  have hm : AEStronglyMeasurable (fun x => ‖f x‖) (μ.restrict S) :=
    hq.aestronglyMeasurable.congr heq
  exact MemLp.of_bound hm C (by simpa only [norm_norm] using hb)

/-- A genuine F-valued continuous function on a measurable compact set is
in L-infinity for the restricted measure, without requiring finite mass. -/
theorem memLp_top_restrict_of_continuousOn_isCompact [OpensMeasurableSpace X]
    (μ : Measure X) {K : Set X} (hK : IsCompact K) (hKm : MeasurableSet K)
    {f : X → F} (hf : ContinuousOn f K) : MemLp f ∞ (μ.restrict K) := by
  obtain ⟨C, _, hb⟩ := (hK.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  apply memLp_top_of_bound (hf.aestronglyMeasurable_of_isCompact hK hKm) C
  filter_upwards [ae_restrict_mem hKm] with x hx
  exact hb _ (Set.mem_image_of_mem _ hx)

end Burnett.Analysis.LocalAeBound
