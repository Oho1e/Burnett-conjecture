import Burnett.Analysis.SignedFourierWindow.CalderonMass

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set Function
open scoped ENNReal

/-- One choice of regions simultaneously gives pointwise reconstruction, the
good-part bound, summable L¹ masses, cancellation and the enlarged exceptional
set estimate. The input is a Borel representative of an integrable function. -/
theorem calderon_decomposition (f : Space → ℂ) (hmf : Measurable f) (hf : Integrable f)
    (a : ℝ≥0∞) (ha : 0 < a) :
    ∃ (u : Set Space) (r : Space → ℝ) (Q : u → Set Space), u.Countable ∧ Pairwise (Disjoint on Q) ∧
      (∀ i : u, MeasurableSet (Q i) ∧ 0 < r i ∧ Q i ⊆ closedBall (i:Space) (4*r i)) ∧
      Measurable (goodPart f Q) ∧ (∀ x, goodPart f Q x + ∑' i, badBlock f (Q i) x = f x) ∧
      (∀ᵐ x ∂volume, ‖goodPart f Q x‖ₑ ≤ a*256) ∧
      (∀ i, Integrable (badBlock f (Q i)) ∧ (∫ x, badBlock f (Q i) x) = 0) ∧
      (∑' i, ∫⁻ x, ‖badBlock f (Q i) x‖ₑ) ≤ 2*∫⁻ x, ‖f x‖ₑ ∧
      a * volume (⋃ i : u, closedBall (i:Space) (8*r i)) ≤ 4096*∫⁻ x, ‖f x‖ₑ := by
  obtain ⟨u,r,Q,hu,hd,geom,cover,lower,upper⟩ := calderon_regions (fun x => ‖f x‖ₑ) hf.2 a ha
  letI : Countable u := hu.to_subtype
  have hm (i : u) := (geom i).1
  have hfin (i : u) : volume (Q i) < ⊤ :=
    (measure_mono (geom i).2.2.2).trans_lt measure_closedBall_lt_top
  have hpos (i : u) : 0 < volume (Q i) :=
    (measure_closedBall_pos volume (i:Space) (geom i).2.1).trans_le (measure_mono (geom i).2.2.1)
  refine ⟨u,r,Q,hu,hd,fun i => ⟨hm i,(geom i).2.1,(geom i).2.2.2⟩,
    goodPart_measurable f hmf Q hm hd,good_add_bad f Q hd,
    good_ae_bound f hf Q hd a cover (fun i => bounded_region_average f (Q i) (hpos i) (hfin i) a (upper i)),
    ?_,(bad_blocks_total f hf Q hm hd hfin).trans (mul_le_mul_left' (setLIntegral_le_lintegral _ _) _),
    eightfold_exceptional_volume hu r (fun i => (geom i).2.1) Q hd (fun i => (geom i).2.2.1) _ a lower⟩
  intro i
  obtain ⟨hi,hz,_⟩ := bad_block_integral f hf (Q i) (hm i) (hfin i)
  exact ⟨hi,hz⟩

end Burnett.Analysis.SignedFourierWindow
