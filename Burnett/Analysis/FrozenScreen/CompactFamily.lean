import Burnett.Analysis.FrozenScreen.Directions
import Burnett.Analysis.FrozenScreen.NullOrthogonality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.V06

open Matrix Set Burnett.RicciSymbol TensorFrame
open scoped Matrix BigOperators

private theorem continuous_dot {X : Type*} [TopologicalSpace X]
    {u v : X → Covector} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => u x ⬝ᵥ v x) := by
  unfold dotProduct
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hu).mul ((continuous_apply i).comp hv)

private theorem continuous_matrix_action {X : Type*} [TopologicalSpace X]
    {A : X → ScreenMatrix} {v : X → Covector} (hA : Continuous A) (hv : Continuous v) :
    Continuous (fun x => A x *ᵥ v x) := by
  apply continuous_pi
  intro i
  change Continuous (fun x => ∑ j, A x i j * v x j)
  exact continuous_finset_sum _ fun j _ =>
    (hA.matrix_elem i j).mul ((continuous_apply j).comp hv)

private theorem continuous_symbolNorm {X : Type*} [TopologicalSpace X]
    {B : X → ScreenMatrix} {e : X → Covector} (hB : Continuous B) (he : Continuous e) :
    Continuous (fun x => symbolNorm (B x) (e x)) := by
  unfold symbolNorm
  exact continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ =>
      ((hB.matrix_elem i j).mul ((continuous_apply i).comp he)).mul
        ((continuous_apply j).comp he)

private theorem continuous_second {X : Type*} [TopologicalSpace X]
    {B : X → ScreenMatrix} {e : X → Covector} (hB : Continuous B) (he : Continuous e) :
    Continuous (fun x => screenSecondDirection (B x) (e x)) := by
  unfold screenSecondDirection
  exact (continuous_matrix_action hB he).sub
    ((continuous_dot he (continuous_matrix_action hB he)).smul he)

private def euclideanUnit : Set Covector := {e | e ⬝ᵥ e = 1}

private theorem compact_euclideanUnit : IsCompact euclideanUnit := by
  have hc : IsClosed euclideanUnit := isClosed_eq (continuous_dot continuous_id continuous_id) continuous_const
  have hb : Bornology.IsBounded (Metric.closedBall (0 : Covector) 1) := Metric.isBounded_closedBall
  apply Metric.isCompact_of_isClosed_isBounded hc (hb.subset ?_)
  intro e he
  change e ⬝ᵥ e = 1 at he
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))).2
  intro i
  have hSum : e i * e i ≤ ∑ j, e j * e j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (e j)) (Finset.mem_univ i)
  change (∑ j, e j * e j) = 1 at he
  rw [he] at hSum
  rw [Real.norm_eq_abs]
  simpa only [abs_one] using
    (sq_le_sq.mp (show (e i)^2 ≤ (1 : ℝ)^2 by simpa only [pow_two, one_mul] using hSum))

private def nullUnit (K : Set ScreenMatrix) : Set (ScreenMatrix × Covector) :=
  (K ×ˢ euclideanUnit) ∩ {p | symbolNorm p.1 p.2 = 0}

private theorem compact_nullUnit (K : Set ScreenMatrix) (hK : IsCompact K) :
    IsCompact (nullUnit K) := by
  exact (hK.prod compact_euclideanUnit).inter_right
    (isClosed_eq (continuous_symbolNorm continuous_fst continuous_snd) continuous_const)

private def nullScreenUnit (K : Set ScreenMatrix) : Set ((ScreenMatrix × Covector) × Covector) :=
  (nullUnit K ×ˢ euclideanUnit) ∩
    ({p | p.2 ⬝ᵥ p.1.2 = 0} ∩ {p | p.2 ⬝ᵥ (p.1.1 *ᵥ p.1.2) = 0})

private theorem compact_nullScreenUnit (K : Set ScreenMatrix) (hK : IsCompact K) :
    IsCompact (nullScreenUnit K) := by
  apply ((compact_nullUnit K hK).prod compact_euclideanUnit).inter_right
  exact (isClosed_eq (continuous_dot continuous_snd (continuous_snd.comp continuous_fst))
    continuous_const).inter (isClosed_eq (continuous_dot continuous_snd
      (continuous_matrix_action (continuous_fst.comp continuous_fst)
        (continuous_snd.comp continuous_fst))) continuous_const)

/-- On the compact unit null family the Euclidean norm squared of the
actual second direction has a uniform positive lower bound. -/
theorem screenSecondDirection_uniform_sq_lower
    (K : Set ScreenMatrix) (hK : IsCompact K) (hInv : ∀ B ∈ K, IsUnit B.det) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B ∈ K, ∀ e : Covector, e ⬝ᵥ e = 1 → symbolNorm B e = 0 →
      δ ≤ screenSecondDirection B e ⬝ᵥ screenSecondDirection B e := by
  let f (p : ScreenMatrix × Covector) :=
    screenSecondDirection p.1 p.2 ⬝ᵥ screenSecondDirection p.1 p.2
  have hc : Continuous f := continuous_dot (continuous_second continuous_fst continuous_snd)
    (continuous_second continuous_fst continuous_snd)
  have hp (p) (hp : p ∈ nullUnit K) : 0 < f p := by
    have he : p.2 ≠ 0 := by
      intro h
      have hu : p.2 ⬝ᵥ p.2 = 1 := hp.1.2
      rw [h, zero_dotProduct] at hu
      norm_num at hu
    have hw := screenSecondDirection_ne_zero_on_null p.1 p.2 (hInv _ hp.1.1) he hp.2
    refine lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) ?_
    exact fun hz => hw (dotProduct_self_eq_zero.mp hz.symm)
  obtain ⟨δ, hδ, hl⟩ := (compact_nullUnit K hK).exists_forall_le' hc.continuousOn hp
  exact ⟨δ, hδ, fun B hB e he hn => hl (B,e) ⟨⟨hB,he⟩,hn⟩⟩

/-- The positive quadratic form on the compact unit null screens has a
uniform lower bound on all Euclidean unit screen vectors. -/
theorem screenQuadratic_uniform_lower
    (K : Set ScreenMatrix) (hK : IsCompact K) (hFrame : ∀ B ∈ K, Nonempty (LorentzFrame B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ B ∈ K, ∀ e v : Covector,
      e ⬝ᵥ e = 1 → symbolNorm B e = 0 → v ⬝ᵥ v = 1 →
      v ⬝ᵥ e = 0 → v ⬝ᵥ (B *ᵥ e) = 0 → c ≤ v ⬝ᵥ (B *ᵥ v) := by
  let f (p : (ScreenMatrix × Covector) × Covector) := p.2 ⬝ᵥ (p.1.1 *ᵥ p.2)
  have hc : Continuous f := continuous_dot continuous_snd
    (continuous_matrix_action (continuous_fst.comp continuous_fst) continuous_snd)
  have hp (p) (hp : p ∈ nullScreenUnit K) : 0 < f p := by
    obtain ⟨⟨⟨⟨hKp, he⟩, hn⟩, hv⟩, hE, hB⟩ := hp
    have hnz {v : Covector} (h : v ⬝ᵥ v = 1) : v ≠ 0 := by
      intro hz
      rw [hz, zero_dotProduct] at h
      norm_num at h
    exact screen_quadratic_pos p.1.1 (Classical.choice (hFrame _ hKp))
      p.1.2 p.2 (hnz he) hn hB hE (hnz hv)
  obtain ⟨c, hc, hl⟩ := (compact_nullScreenUnit K hK).exists_forall_le' hc.continuousOn hp
  exact ⟨c, hc, fun B hB e v he hn hv hE hW => hl ((B,e),v) ⟨⟨⟨⟨hB,he⟩,hn⟩,hv⟩,hE,hW⟩⟩


/-- A closed sublevel region on a compact set stays a positive distance
in the defining function from a level where a strict bound holds. -/
private theorem positive_neighborhood_of_zero {X : Type*} [TopologicalSpace X]
    (S : Set X) (hS : IsCompact S) (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (a : ℝ) (h : ∀ p ∈ S, f p = 0 → a < g p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, |f p| < ε → a < g p := by
  let bad := S ∩ {p | g p ≤ a}
  have hbad : IsCompact bad := hS.inter_right (isClosed_le hg continuous_const)
  have hp (p : X) (hpb : p ∈ bad) : 0 < |f p| :=
    abs_pos.mpr (fun h0 => (not_lt_of_ge hpb.2) (h p hpb.1 h0))
  obtain ⟨ε, hε, hsep⟩ := hbad.exists_forall_le' hf.abs.continuousOn hp
  refine ⟨ε, hε, fun p hp hpNear => ?_⟩
  exact lt_of_not_ge (fun hpBad => (not_le_of_gt hpNear) (hsep p ⟨hp,hpBad⟩))

/-- The two strictly positive null-screen bounds persist on one uniform
neighborhood of the unit null set of a compact Lorentz family. -/
theorem exists_uniform_wide_screen_bounds
    (K : Set ScreenMatrix) (hK : IsCompact K)
    (hInv : ∀ B ∈ K, IsUnit B.det) (hFrame : ∀ B ∈ K, Nonempty (LorentzFrame B)) :
    ∃ ε δ c : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < c ∧
      ∀ B ∈ K, ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm B e| < ε →
        δ ≤ screenSecondDirection B e ⬝ᵥ screenSecondDirection B e ∧
        ∀ v : Covector, v ⬝ᵥ v = 1 → v ⬝ᵥ e = 0 → v ⬝ᵥ (B *ᵥ e) = 0 → c ≤ v ⬝ᵥ (B *ᵥ v) := by
  obtain ⟨δ, hδ, hδNull⟩ := screenSecondDirection_uniform_sq_lower K hK hInv
  obtain ⟨c, hc, hcNull⟩ := screenQuadratic_uniform_lower K hK hFrame
  let S₁ := K ×ˢ euclideanUnit
  let f₁ (p : ScreenMatrix × Covector) := symbolNorm p.1 p.2
  let g₁ (p : ScreenMatrix × Covector) :=
    screenSecondDirection p.1 p.2 ⬝ᵥ screenSecondDirection p.1 p.2
  have hg₁ : Continuous g₁ := continuous_dot (continuous_second continuous_fst continuous_snd)
    (continuous_second continuous_fst continuous_snd)
  have hNull₁ (p) (hp : p ∈ S₁) (hzero : f₁ p = 0) : δ / 2 < g₁ p :=
    (by linarith : δ / 2 < δ).trans_le (hδNull p.1 hp.1 p.2 hp.2 hzero)
  obtain ⟨ε₁, hε₁, hNear₁⟩ := positive_neighborhood_of_zero S₁
    (hK.prod compact_euclideanUnit) f₁ g₁ (continuous_symbolNorm continuous_fst continuous_snd)
    hg₁ (δ / 2) hNull₁
  let S₂ : Set ((ScreenMatrix × Covector) × Covector) := (S₁ ×ˢ euclideanUnit) ∩
    ({p | p.2 ⬝ᵥ p.1.2 = 0} ∩ {p | p.2 ⬝ᵥ (p.1.1 *ᵥ p.1.2) = 0})
  have hS₂ : IsCompact S₂ :=
    ((hK.prod compact_euclideanUnit).prod compact_euclideanUnit).inter_right
      ((isClosed_eq (continuous_dot continuous_snd (continuous_snd.comp continuous_fst))
        continuous_const).inter (isClosed_eq (continuous_dot continuous_snd
          (continuous_matrix_action (continuous_fst.comp continuous_fst)
            (continuous_snd.comp continuous_fst))) continuous_const))
  let f₂ (p : (ScreenMatrix × Covector) × Covector) := symbolNorm p.1.1 p.1.2
  let g₂ (p : (ScreenMatrix × Covector) × Covector) := p.2 ⬝ᵥ (p.1.1 *ᵥ p.2)
  have hg₂ : Continuous g₂ := continuous_dot continuous_snd
    (continuous_matrix_action (continuous_fst.comp continuous_fst) continuous_snd)
  have hNull₂ (p) (hp : p ∈ S₂) (hzero : f₂ p = 0) : c / 2 < g₂ p :=
    (by linarith : c / 2 < c).trans_le
      (hcNull p.1.1 hp.1.1.1 p.1.2 p.2 hp.1.1.2 hzero hp.1.2 hp.2.1 hp.2.2)
  obtain ⟨ε₂, hε₂, hNear₂⟩ := positive_neighborhood_of_zero S₂ hS₂ f₂ g₂
    (continuous_symbolNorm (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst))
    hg₂ (c / 2) hNull₂
  refine ⟨min ε₁ ε₂, δ / 2, c / 2, lt_min hε₁ hε₂, by positivity, by positivity, ?_⟩
  intro B hB e he hNear
  refine ⟨(hNear₁ (B,e) ⟨hB,he⟩ (hNear.trans_le (min_le_left _ _))).le, ?_⟩
  intro v hv hE hW
  exact (hNear₂ ((B,e),v) ⟨⟨⟨hB,he⟩,hv⟩,hE,hW⟩ (hNear.trans_le (min_le_right _ _))).le

end Burnett.V06
