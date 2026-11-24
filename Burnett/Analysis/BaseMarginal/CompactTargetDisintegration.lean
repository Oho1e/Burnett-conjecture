import Burnett.Analysis.FiberDisintegration.Weighted
import Mathlib.Topology.Metrizable.Urysohn

/-! Disintegration in an ambient target through its actual compact support. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 2700000

noncomputable section
namespace Burnett.F08.FiberGluing

open Function Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

open private finite_weighted_conditional from Burnett.Analysis.FiberDisintegration.Weighted

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- A finite graph measure supported in a compact output window disintegrates
over the original volume. The kernel takes values in the original ambient target. -/
theorem exists_finite_graphDisintegration_of_compact_target (v : Measure X) [IsFiniteMeasure v]
    (μ : Measure Y) [IsFiniteMeasure μ] (π : Y → X) (hπ : Measurable π)
    {K : Set Y} (hK : IsCompact K) (hSupp : μ Kᶜ = 0)
    (w : X → ℝ≥0∞) (hw : Measurable w) (hMarg : μ.map π = v.withDensity w)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hb : ∀ x, w x ≤ C) :
    ∃ κ : Kernel X Y, IsFiniteKernel κ ∧ v ⊗ₘ κ = μ.map (fun y => (π y, y)) ∧
      ∀ᵐ x ∂v, κ x univ = w x := by
  classical
  cases isEmpty_or_nonempty K with
  | inl hE =>
    have h0 : K = ∅ := eq_empty_iff_forall_notMem.mpr (fun y hy => hE.false ⟨y, hy⟩)
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp (by simpa only [h0, compl_empty] using hSupp)
    have hV : v.withDensity w = 0 := hMarg.symm.trans (by rw [hμ0, Measure.map_zero])
    refine ⟨0, inferInstance, by simp [hμ0], ?_⟩
    exact ((withDensity_eq_zero_iff hw.aemeasurable).mp hV).mono fun x hx => by simp [hx]
  | inr hN =>
    letI : Nonempty K := hN
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
    haveI : PolishSpace K := inferInstance
    let j : K → Y := Subtype.val
    have hj : MeasurableEmbedding j := MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet
    let ν := μ.comap j
    have hMap : ν.map j = μ := by
      change (μ.comap j).map j = μ
      rw [hj.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hSupp)
    letI : IsFiniteMeasure (ν.map j) := by rw [hMap]; infer_instance
    letI : IsFiniteMeasure ν := Measure.isFiniteMeasure_of_map hj.measurable.aemeasurable
    let g (y : K) := (π (j y), y)
    have hg : Measurable g := (hπ.comp hj.measurable).prodMk measurable_id
    let ρ := ν.map g
    letI : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map ν g
    have hFst : ρ.fst = v.withDensity w := by
      calc
        _ = ν.map (π ∘ j) := Measure.fst_map_prodMk measurable_id
        _ = _ := by rw [← Measure.map_map hπ hj.measurable, hMap, hMarg]
    obtain ⟨κ, hκ, hJoint, hTotal⟩ := finite_weighted_conditional v ρ w hw C hC hb hFst
    letI : IsFiniteKernel κ := hκ
    have hprod : Measurable (Prod.map id j : X × K → X × Y) := measurable_id.prodMap hj.measurable
    have hMapped : v ⊗ₘ κ.map j = (v ⊗ₘ κ).map (Prod.map id j) := by
      ext U hU
      rw [Measure.compProd_apply hU, Measure.map_apply hprod hU, Measure.compProd_apply (hprod hU)]
      apply lintegral_congr
      intro x
      rw [Kernel.map_apply' κ hj.measurable x (measurable_prodMk_left hU)]
      rfl
    refine ⟨κ.map j, inferInstance, ?_, Eventually.of_forall fun x => ?_⟩
    · rw [hMapped, hJoint]
      change (ν.map g).map (Prod.map id j) = _
      rw [Measure.map_map hprod hg, ← hMap]
      exact (Measure.map_map (hπ.prodMk measurable_id) hj.measurable).symm
    · rw [Kernel.map_apply κ hj.measurable, Measure.map_apply hj.measurable MeasurableSet.univ,
        preimage_univ, hTotal]

end Burnett.F08.FiberGluing
