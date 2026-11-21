import Burnett.Analysis.PrincipalEnergy.Localization.FixedLatticeCutoffs
import Burnett.Analysis.PrincipalEnergy.Localization.UniformCompactH1Pair
import Burnett.Analysis.PrincipalEnergy.Localization.FiniteCutoffEnergy

set_option autoImplicit false
set_option maxHeartbeats 5900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Set Function Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff

/-- A real radial Schwartz cutoff with the supplied inner and outer radii. -/
theorem exists_radialSchwartzCutoff (ri ro : ℝ) (hi : 0 < ri) (ho : ri < ro) :
    ∃ χ : SchwartzMap Space ℂ, HasCompactSupport (χ : Space → ℂ) ∧
      tsupport (χ : Space → ℂ) ⊆ closedBall (0 : Space) ro ∧
      (∀ x, χ x = ((χ x).re : ℂ) ∧ 0 ≤ (χ x).re ∧ (χ x).re ≤ 1) ∧
      ∀ x, ‖x‖ ≤ ri → χ x = 1 := by
  let b : ContDiffBump (0 : Space) := ⟨ri, ro, hi, ho⟩
  let q (x : Space) := (b x : ℂ)
  have hk : HasCompactSupport q := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ := hk.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨χ, hk, ?_, ?_, ?_⟩
  · change tsupport q ⊆ closedBall (0 : Space) ro
    have hEq : support q = support (b : Space → ℝ) := by
      ext x
      simp [q, mem_support]
    rw [show tsupport q = tsupport (b : Space → ℝ) from congrArg closure hEq, b.tsupport_eq]
  · intro x
    change (b x : ℂ) = ((↑(b x) : ℂ).re : ℂ) ∧ 0 ≤ (b x : ℂ).re ∧ (b x : ℂ).re ≤ 1
    rw [Complex.ofReal_re]
    exact ⟨rfl, b.nonneg, b.le_one⟩
  · intro x hx
    change (b x : ℂ) = 1
    rw [b.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hx)]
    exact Complex.ofReal_one

/-- Every point meets at most a fixed number of the radius-five supports
on the original lattice. -/
theorem sum_latticeCutoff_values_sq_le (s : Finset LatticeIndex)
    (q : ↥s → SchwartzMap Space ℂ) (R : ℝ)
    (hsupp : ∀ i, tsupport (q i : Space → ℂ) ⊆ closedBall (latticeCenter i.val) 5)
    (hSup : ∀ i x, ‖q i x‖ ≤ R) (x : Space) :
    (∑ i, ‖q i x‖^2) ≤ ((17^4 : ℕ) : ℝ) * R^2 := by
  classical
  have hx : x ∈ ⋃ a : LatticeIndex, ball (latticeCenter a) 3 := by rw [lattice_ball_cover]; trivial
  obtain ⟨a, ha⟩ := mem_iUnion.mp hx
  let t : Finset ↥s := Finset.univ.filter fun i => latticeNear a i.val
  have hNear (i : ↥s) (hi : x ∈ closedBall (latticeCenter i.val) 5) : latticeNear a i.val := by
    have hd := dist_triangle (latticeCenter a) x (latticeCenter i.val)
    rw [dist_comm _ x] at hd
    have hDist : dist (latticeCenter a) (latticeCenter i.val) ≤ 8 := by
      have hb : dist x (latticeCenter a) < 3 := mem_ball.mp ha
      rw [mem_closedBall] at hi
      linarith only [hd, hb, hi]
    intro j
    have h := (PiLp.dist_apply_le (latticeCenter a) (latticeCenter i.val) j).trans hDist
    change dist (a j : ℝ) (i.val j : ℝ) ≤ 8 at h
    rw [Real.dist_eq] at h
    exact_mod_cast h
  have hCard : t.card ≤ 17^4 := by
    refine (Finset.card_le_card_of_injOn (t := s.filter fun b => latticeNear a b)
      (fun i : ↥s => i.val) ?_ ?_).trans (lattice_pair_degree s a)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨i.property, (Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ h
      exact Subtype.ext h
  have hSum : (∑ i : ↥s, ‖q i x‖^2) = ∑ i ∈ t, ‖q i x‖^2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ t) fun i _ hi => ?_
    have hz : q i x = 0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNear i (hsupp i (subset_closure hne))⟩)
    rw [hz, norm_zero, zero_pow (by norm_num)]
  rw [hSum]
  calc
    _ ≤ ∑ _i ∈ t, R^2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hSup i x) 2
    _ = (t.card : ℝ) * R^2 := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (sq_nonneg _)

private theorem schwartz_sq_norm_integral (f : SchwartzMap Space ℂ) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [l2_norm_sq_integral]
  exact integral_congr_ae ((f.coeFn_toLp 2 volume).fun_comp fun z => ‖z‖ ^ 2)

/-- A pointwise square-sum bound of multiplying cutoffs is inherited by
the sum of squared Lebesgue L² norms of the cut test. -/
theorem scalarCutoff_sum_L2_sq_le_of_square_bound {ι : Type*} [Fintype ι]
    (q : ι → SchwartzMap Space ℂ) (f : SchwartzMap Space ℂ) (B : ℝ)
    (h : ∀ x, ∑ i, ‖q i x‖^2 ≤ B) :
    (∑ i, ‖(scalarSchwartzProduct (q i) f).toLp 2 volume‖^2) ≤ B * ‖f.toLp 2 volume‖^2 := by
  let F (i : ι) := scalarSchwartzProduct (q i) f
  have hi (u : SchwartzMap Space ℂ) : Integrable (fun x => ‖u x‖^2) :=
    (u.memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simp_rw [schwartz_sq_norm_integral]
  rw [← integral_finset_sum Finset.univ (fun i _ => hi (F i)), ← integral_const_mul]
  apply integral_mono (integrable_finset_sum Finset.univ (fun i _ => hi (F i))) ((hi f).const_mul B)
  intro x
  simp only [F, scalarSchwartzProduct_apply, norm_mul, mul_pow, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (h x) (sq_nonneg _)

end Burnett.Analysis.CarlesonEmbedding
