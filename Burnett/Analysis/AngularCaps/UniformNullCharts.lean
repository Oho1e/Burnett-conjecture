import Burnett.Analysis.AngularCaps.ProjectiveNullGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set Metric
open scoped BigOperators

theorem chartBox_isCompact (i : Index) : IsCompact (chartBox i) := by
  have hEq : chartBox i = {x : Vec | x i = 1} ∩ ⋂ j : Index, {x : Vec | |x j| ≤ 1} := by
    ext x
    simp only [chartBox, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  have hClosed : IsClosed (chartBox i) := by
    rw [hEq]
    apply (isClosed_eq (PiLp.continuous_apply 2 (fun _ : Index => ℝ) i) continuous_const).inter
    exact isClosed_iInter fun j => isClosed_le
      ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) j).abs) continuous_const
  refine (isCompact_closedBall (0 : Vec) 2).of_isClosed_subset hClosed fun x hx => ?_
  rw [mem_closedBall, dist_zero_right]
  exact (norm_le_twice_of_coordinates x 1 zero_le_one hx.2).trans_eq (mul_one _)

private theorem continuous_pair_row (j : Index) :
    Continuous fun p : Form × Vec => rowValue p.1 p.2 j := by
  unfold rowValue
  apply continuous_finset_sum
  intro i _
  have hi' : Continuous fun p : Form × Vec => p.1 i := (continuous_apply i).comp continuous_fst
  have hi : Continuous fun p : Form × Vec => p.1 i j := (continuous_apply j).comp hi'
  exact hi.mul ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) i).comp continuous_snd)

private theorem continuous_pair_quadratic : Continuous fun p : Form × Vec => quadratic p.1 p.2 := by
  unfold quadratic pairing
  exact continuous_finset_sum _ fun j _ =>
    (continuous_pair_row j).mul ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) j).comp continuous_snd)

private def nullChartDomain (K : Set Form) (i : Index) : Set (Form × Vec) :=
  (K ×ˢ chartBox i) ∩ {p | quadratic p.1 p.2 = 0}

private theorem nullChartDomain_compact {K : Set Form} (hK : IsCompact K) (i : Index) :
    IsCompact (nullChartDomain K i) :=
  (hK.prod (chartBox_isCompact i)).inter_right (isClosed_eq continuous_pair_quadratic continuous_const)

private def axisSize (i : Index) (p : Form × Vec) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, |rowValue p.1 p.2 j|

private theorem axisSize_pos {K : Set Form}
    (hND : ∀ m ∈ K, Nondegenerate m) {i : Index} {p : Form × Vec}
    (hp : p ∈ nullChartDomain K i) : 0 < axisSize i p := by
  have hm : p.1 ∈ K := hp.1.1
  have hx : p.2 ∈ chartBox i := hp.1.2
  have hQ : quadratic p.1 p.2 = 0 := hp.2
  by_contra! hNot
  have hZero (j : Index) (hj : j ≠ i) : rowValue p.1 p.2 j = 0 := by
    apply abs_nonpos_iff.mp
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (rowValue p.1 p.2 k))
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)).trans hNot
  have hAt : rowValue p.1 p.2 i = 0 := by
    unfold quadratic pairing at hQ
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hZero j hj, zero_mul])
      (fun h => (h (Finset.mem_univ i)).elim), hx.1, mul_one] at hQ
    exact hQ
  have hX := hND p.1 hm p.2 (fun j => by
    by_cases hj : j = i
    · rw [hj]
      exact hAt
    · exact hZero j hj)
  have he : (1 : ℝ) = 0 := by
    exact hx.1.symm.trans (congrArg (fun x : Vec => x i) hX)
  exact one_ne_zero he

private theorem axisSize_uniform_positive {K : Set Form} (hK : IsCompact K)
    (hND : ∀ m ∈ K, Nondegenerate m) (i : Index) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ nullChartDomain K i, a ≤ axisSize i p := by
  by_cases h : (nullChartDomain K i).Nonempty
  · have hc : Continuous (axisSize i) :=
      continuous_finset_sum _ fun j _ => (continuous_pair_row j).abs
    obtain ⟨p, hp, hmin⟩ := (nullChartDomain_compact hK i).exists_isMinOn h hc.continuousOn
    exact ⟨axisSize i p, axisSize_pos hND hp, fun t ht => (isMinOn_iff.mp hmin) t ht⟩
  · exact ⟨1, zero_lt_one, fun p hp => (h ⟨p,hp⟩).elim⟩

/-- Compactness and nondegeneracy give one lower bound for a transverse
coordinate derivative on every true affine projective null chart. -/
theorem exists_uniform_transverse_axis {K : Set Form} (hK : IsCompact K)
    (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ a : ℝ, 0 < a ∧ ∀ m ∈ K, ∀ i (x : Vec), x ∈ chartBox i → quadratic m x = 0 →
      ∃ j : Index, j ≠ i ∧ a ≤ |rowValue m x j| := by
  choose s hs hLower using axisSize_uniform_positive hK hND
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ s Finset.univ_nonempty
  let a := s i₀ / 4
  refine ⟨a, div_pos (hs i₀) (by norm_num), fun m hm i x hx hQ => ?_⟩
  have hp : (m,x) ∈ nullChartDomain K i := ⟨⟨hm, hx⟩, hQ⟩
  have hlow : s i₀ ≤ axisSize i (m,x) := (hmin i (Finset.mem_univ i)).trans (hLower i (m,x) hp)
  by_contra! hAll
  have hUp : axisSize i (m,x) ≤ 3*a := by
    unfold axisSize
    calc
      _ ≤ ∑ _ ∈ (Finset.univ.erase i), a :=
        Finset.sum_le_sum fun j hj => (hAll j (Finset.mem_erase.mp hj).1).le
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat]
  have hAt := hlow.trans hUp
  dsimp only [a] at hAt
  linarith only [hAt, hs i₀]

/-- A uniform upper row bound from the fixed compact coefficient set. -/
theorem exists_uniform_row_bound {K : Set Form} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m ∈ K, ∀ x : Vec, ‖x‖ ≤ 2 → ∀ j, |rowValue m x j| ≤ B := by
  let A := K ×ˢ closedBall (0 : Vec) 2
  have hA : IsCompact A := hK.prod (isCompact_closedBall _ _)
  choose M hM using fun j : Index => (hA.image (continuous_pair_row j)).isBounded.exists_norm_le
  let B := 1 + ∑ j, max (M j) 0
  have hB : (0 : ℝ) < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun j _ => le_max_right _ _))
  refine ⟨B, hB, fun m hm x hx j => ?_⟩
  have hmX : (m,x) ∈ A := ⟨hm, by simpa only [mem_closedBall, dist_zero_right] using hx⟩
  have h := hM j (rowValue m x j) ⟨(m,x), hmX, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans ((le_max_left _ _).trans
    ((Finset.single_le_sum (fun k _ => le_max_right (M k) 0) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)))

end Burnett.Analysis.ProjectiveNullCaps
