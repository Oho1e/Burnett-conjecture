import Burnett.Analysis.FrozenTransport.GaugeCorrection.DominatedIntegralJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

section

variable {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure Y)

omit [SecondCountableTopology Y] in
private theorem compact_support_parameter_jet_local_bound
    (F : Y → X → V) (s : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set Y) (hK : IsCompact K) (finite : μ K < ⊤)
    (support : ∀ y ∉ K, F y = 0) (n : ℕ) (q : X) :
    ∃ w : Y → ℝ, Integrable w μ ∧ ∀ q' ∈ ball q 1, ∀ y : Y,
      ‖iteratedFDeriv ℝ n (F y) q'‖ ≤ w y := by
  let g (z : Y × X) : ℝ := ‖iteratedFDeriv ℝ n (F z.1) z.2‖
  have cc : IsCompact (K ×ˢ closedBall q 1) := hK.prod (isCompact_closedBall q 1)
  have gc : Continuous g := (smooth_right_slice_iterated_fderiv F s n).continuous.norm
  obtain ⟨C,cb⟩ := cc.bddAbove_image gc.continuousOn
  let w := K.indicator (fun _ : Y => C)
  have wi : Integrable w μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const finite.ne)
  refine ⟨w,wi,fun q' hq' y => ?_⟩
  by_cases yin : y ∈ K
  · have qb : q' ∈ closedBall q 1 := ball_subset_closedBall hq'
    have b : g (y,q') ≤ C := cb (mem_image_of_mem g ⟨yin,qb⟩)
    change g (y,q') ≤ w y
    rw [show w y = C from indicator_of_mem yin _]
    exact b
  · have zero : F y = (fun _ : X => (0 : V)) := support y yin
    rw [zero,iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero,
      show w y = 0 from indicator_of_notMem yin _]

/-- Uniform compact support in the integrated variable gives genuine
local domination of every parameter jet by compactness. -/
theorem dominated_integral_jets_of_uniform_compact_support
    (F : Y → X → V) (s : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set Y) (hK : IsCompact K) (finite : μ K < ⊤)
    (support : ∀ y ∉ K, F y = 0) :
    DominatedIntegralJets μ (fun x y => F y x) := by
  have sectionSmooth (y : Y) : ContDiff ℝ ∞ (F y) :=
    s.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨sectionSmooth,fun n q => ?_,fun n q => ?_⟩
  · have j := smooth_right_slice_iterated_fderiv F s n
    exact (j.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · obtain ⟨w,wi,b⟩ := compact_support_parameter_jet_local_bound μ F s K hK finite support n q
    exact ⟨1,zero_lt_one,w,wi,b⟩

end

end Burnett.A03
