import Burnett.Geometry.Causality.FutureCurveSecants

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

/-- A transitive relation on a real-parametrized path holds across a compact
interval when each central point is related to both adjacent sides. -/
theorem interval_relation_of_local_steps {X : Type*} {R : X → X → Prop}
    (hTrans : Transitive R) (γ : ℝ → X) {a b : ℝ} (hab : a < b)
    (hLocal : ∀ s ∈ Icc a b, ∀ᶠ t in 𝓝[≠] s,
      (s < t → R (γ s) (γ t)) ∧ (t < s → R (γ t) (γ s))) : R (γ a) (γ b) := by
  let S := {t : ℝ | t ∈ Icc a b ∧ (t = a ∨ R (γ a) (γ t))}
  have ha : a ∈ S := ⟨left_mem_Icc.mpr hab.le, Or.inl rfl⟩
  have hS : BddAbove S := ⟨b, fun _ ht => ht.1.2⟩
  let m := sSup S
  have hm : m ∈ Icc a b := ⟨le_csSup hS ha, csSup_le ⟨a, ha⟩ (fun _ ht => ht.1.2)⟩
  obtain ⟨ε, hε, hnear⟩ := Metric.mem_nhdsWithin_iff.mp (hLocal m hm)
  have hStep (t : ℝ) (ht : t ∈ Metric.ball m ε) (hne : t ≠ m) :
      (m < t → R (γ m) (γ t)) ∧ (t < m → R (γ t) (γ m)) :=
    hnear (show t ∈ Metric.ball m ε ∩ {m}ᶜ from ⟨ht, hne⟩)
  have hmS : m ∈ S := by
    by_contra hnot
    have hGap : m - ε < sSup S := sub_lt_self m hε
    obtain ⟨t, ht, hNear⟩ := exists_lt_of_lt_csSup ⟨a, ha⟩ hGap
    have hle : t ≤ m := le_csSup hS ht
    have hlt : t < m := lt_of_le_of_ne hle (fun hEq => hnot (hEq ▸ ht))
    have hBall : t ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    have htm := (hStep t hBall hlt.ne).2 hlt
    have hmRel : R (γ a) (γ m) := ht.2.elim (fun he => he ▸ htm) (fun h => hTrans h htm)
    exact hnot ⟨hm, Or.inr hmRel⟩
  have hmb : m = b := by
    by_contra hne
    have hlt : m < b := lt_of_le_of_ne hm.2 hne
    let d := min (ε / 2) ((b - m) / 2)
    have hd : 0 < d := lt_min (half_pos hε) (half_pos (sub_pos.mpr hlt))
    let t := m + d
    have ht : m < t := lt_add_of_pos_right m hd
    have htI : t ∈ Icc a b := ⟨hm.1.trans ht.le, by
      have hdb : d ≤ (b - m) / 2 := min_le_right _ _
      change m + d ≤ b
      linarith⟩
    have hBall : t ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.le)]
      have hdε : d ≤ ε / 2 := min_le_left _ _
      change m + d - m < ε
      linarith
    have hmt := (hStep t hBall ht.ne').1 ht
    have htRel : R (γ a) (γ t) := hmS.2.elim (fun he => he ▸ hmt) (fun h => hTrans h hmt)
    exact (not_le_of_gt ht) (le_csSup hS (show t ∈ S from ⟨htI, Or.inr htRel⟩))
  have hbS : b ∈ S := hmb ▸ hmS
  exact hbS.2.resolve_left hab.ne'

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A path with everywhere future timelike tangent on a finite interval
has chronologically ordered endpoints in the actual preferred-chart relation. -/
theorem chartChronology_of_regular_future_timelike_curve {g : Field (M := M)}
    (hg : IsSmooth g) (o : TimeOrientation g) (γ : ℝ → M) {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ Icc a b, ∃ v : TangentSpace Model (γ t),
      HasMFDerivAt 𝓘(ℝ) Model γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
      g (γ t) v v < 0 ∧ g (γ t) (o.vector (γ t)) v < 0) :
    (γ a, γ b) ∈ chartChronology o := by
  let R := fun x y : M => (x, y) ∈ chartChronology o
  have hTrans : Transitive R := fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂
  apply interval_relation_of_local_steps hTrans γ hab
  intro t ht
  obtain ⟨v, hd, hv, ho⟩ := hγ t ht
  exact eventually_chartChronology_of_intrinsic_derivative hg o γ t v hd hv ho

end Burnett.Geometry.FiniteCausalVolume
