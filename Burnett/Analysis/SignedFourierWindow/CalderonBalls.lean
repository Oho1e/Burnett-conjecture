import Burnett.Analysis.CenteredMaximal.MaximalLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set
open scoped ENNReal

private def above (g : Space → ℝ≥0∞) (level : ℝ≥0∞) (x : Space) (r : ℝ) : Prop :=
  level * volume (closedBall x r) < ∫⁻ y in closedBall x r, g y

private theorem bounded_radii (g : Space → ℝ≥0∞) (hg : (∫⁻ y, g y) < ⊤)
    (a : ℝ≥0∞) (ha : 0<a) : ∃ R : ℝ, 0<R ∧ ∀ (x : Space) (r : ℝ), above g a x r → r ≤ R := by
  have mon : Monotone (fun n : ℕ => closedBall (0:Space) (n:ℝ)) :=
    fun i j hij => closedBall_subset_closedBall (by exact_mod_cast hij)
  have hu : (⨆ n : ℕ, volume (closedBall (0:Space) (n:ℝ))) = ⊤ := by
    rw [← mon.measure_iUnion, iUnion_closedBall_nat, measure_univ_of_isAddLeftInvariant]
  have bigger : (∫⁻ y,g y) < a * ⨆ n : ℕ, volume (closedBall (0:Space) (n:ℝ)) := by
    rwa [hu,ENNReal.mul_top ha.ne']
  rw [ENNReal.mul_iSup,lt_iSup_iff] at bigger
  obtain ⟨n,hn⟩ := bigger
  refine ⟨(n:ℝ)+1,by positivity,?_⟩
  intro x r h
  by_contra! hr
  have hvol : volume (closedBall (0:Space) (n:ℝ)) ≤ volume (closedBall x r) := by
    rw [Measure.addHaar_closedBall_center volume x]
    exact measure_mono (closedBall_subset_closedBall (by linarith))
  exact (not_lt_of_ge (setLIntegral_le_lintegral _ _)) ((hn.trans_le (mul_le_mul_left' hvol a)).trans h)

private theorem last_crossing (g : Space → ℝ≥0∞) (a : ℝ≥0∞) (x : Space) (R : ℝ)
    (bound : ∀ r : ℝ, above g a x r → r ≤ R) (r : ℝ) (hr : 0<r) (first : above g a x r) :
    ∃ s : ℝ, 0<s ∧ above g a x s ∧ ¬ above g a x (4*s) := by
  by_contra! none
  have all (n : ℕ) : above g a x ((4:ℝ)^n*r) := by
    induction n with
    | zero => simpa using first
    | succ n ih =>
      simpa only [pow_succ',mul_assoc] using none ((4:ℝ)^n*r) (by positivity) ih
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (R/r) (by norm_num : (1:ℝ)<4)
  exact (not_lt_of_ge (bound _ (all n))) ((div_lt_iff₀ hr).mp hn)

/-- A disjoint countable selection at the last superlevel crossing. The
four-fold enlarged balls cover the maximal superlevel set. Their averages
already satisfy the upper threshold, while each inner ball exceeds it. -/
theorem calderon_ball_selection (g : Space → ℝ≥0∞) (hg : (∫⁻ y,g y) < ⊤) (a : ℝ≥0∞) (ha : 0<a) :
    ∃ (u : Set Space) (r : Space → ℝ), u.Countable ∧ u.PairwiseDisjoint (fun x => closedBall x (r x)) ∧
      {x | a < centeredMax g x} ⊆ ⋃ x ∈ u, closedBall x (4*r x) ∧
      (∀ x ∈ u, 0<r x ∧ a * volume (closedBall x (r x)) < ∫⁻ y in closedBall x (r x), g y) ∧
      (∀ x ∈ u, (∫⁻ y in closedBall x (4*r x), g y) ≤ a*volume (closedBall x (4*r x))) := by
  classical
  obtain ⟨R,_,bound⟩ := bounded_radii g hg a ha
  let T := {x | a < centeredMax g x}
  have chooseR (x : Space) (hx : x ∈ T) : ∃ s : ℝ, 0<s ∧ above g a x s ∧ ¬ above g a x (4*s) := by
    obtain ⟨r,hr,h⟩ := (centeredMax_level g a x).mp hx
    exact last_crossing g a x R (bound x) r hr h
  choose! r hr using chooseR
  obtain ⟨u,sub,disj,cover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T id r R
    (fun x hx => bound x (r x) (hr x hx).2.1) 4 (by norm_num)
  change u.PairwiseDisjoint (fun x => closedBall x (r x)) at disj
  have openDisj : u.PairwiseDisjoint (fun x => ball x (r x)) :=
    fun x hx y hy h => (disj hx hy h).mono ball_subset_closedBall ball_subset_closedBall
  have count := openDisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x,mem_ball_self (hr x (sub hx)).1⟩)
  refine ⟨u,r,count,disj,?_,fun x hx => ⟨(hr x (sub hx)).1,(hr x (sub hx)).2.1⟩,
    fun x hx => le_of_not_gt (hr x (sub hx)).2.2⟩
  intro x hx
  obtain ⟨y,hy,H⟩ := cover x hx
  exact mem_iUnion₂.mpr ⟨y,hy,H (mem_closedBall_self (hr x hx).1.le)⟩

end Burnett.Analysis.SignedFourierWindow
