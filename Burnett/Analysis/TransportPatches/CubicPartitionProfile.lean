import Burnett.Analysis.PrincipalEnergy.Localization.FixedLatticeCutoffs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! One compactly supported smooth profile whose cubed lattice translates
sum to one. All localizations can use translates and dilates of this profile. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.C01

open Set Function Filter Metric Burnett.Analysis.CarlesonEmbedding
open scoped ContDiff Manifold BigOperators Topology

private theorem latticeCenter_add (a b : LatticeIndex) :
    latticeCenter (a + b) = latticeCenter a + latticeCenter b := by
  ext i
  change ((a i + b i : ℤ) : ℝ) = (a i : ℝ) + (b i : ℝ)
  exact Int.cast_add ..

private theorem latticeNear_finite (b : LatticeIndex) : {a | latticeNear a b}.Finite := by
  let offset (a : {a | latticeNear a b}) (i : Fin 4) : Fin 17 :=
    ⟨(a.val i - b i + 8).toNat, by
      obtain ⟨hl, hu⟩ := abs_le.mp (a.property i)
      omega⟩
  have hInjective : Injective offset := by
    intro a a' eq
    apply Subtype.ext
    funext i
    have h := congrArg (fun f : Fin 4 → Fin 17 => (f i).val) eq
    change (a.val i - b i + 8).toNat = (a'.val i - b i + 8).toNat at h
    have ha := (abs_le.mp (a.property i)).1
    have ha' := (abs_le.mp (a'.property i)).1
    omega
  letI : Finite {a | latticeNear a b} := Finite.of_injective offset hInjective
  exact Set.toFinite _

theorem latticeNear_floor_of_dist_le_seven (a : LatticeIndex) (x : LatticeSpace)
    (hDist : dist (latticeCenter a) x ≤ 7) :
    latticeNear a (fun i => Int.floor (x i)) := by
  intro i
  have hCoord := (PiLp.dist_apply_le (latticeCenter a) x i).trans hDist
  change dist (a i : ℝ) (x i) ≤ 7 at hCoord
  rw [Real.dist_eq] at hCoord
  have hFloor : |x i - (Int.floor (x i) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    exact (Int.fract_lt_one (x i)).le
  have h := (abs_sub_le (a i : ℝ) (x i) (Int.floor (x i) : ℝ)).trans (add_le_add hCoord hFloor)
  exact_mod_cast h

/-- The enlarged balls used for the outer cutoffs are locally finite. -/
theorem locallyFinite_latticeClosedBall :
    LocallyFinite (fun a : LatticeIndex => closedBall (latticeCenter a) 6) := by
  intro x
  let b : LatticeIndex := fun i => Int.floor (x i)
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, (latticeNear_finite b).subset ?_⟩
  rintro a ⟨y, hy, hx⟩
  have hDist : dist (latticeCenter a) x ≤ 7 := by
    have hFirst : dist (latticeCenter a) y ≤ 6 := by
      rw [dist_comm]
      exact hy
    have hNext : dist y x < 1 := hx
    linarith [dist_triangle (latticeCenter a) y x]
  exact latticeNear_floor_of_dist_le_seven a x hDist

private def bump : ContDiffBump (0 : LatticeSpace) := ⟨3, 4, by norm_num, by norm_num⟩

private def bumpCube (x : LatticeSpace) (a : LatticeIndex) : ℝ :=
  bump (x - latticeCenter a) ^ 3

private def cubeSum (x : LatticeSpace) : ℝ := ∑ᶠ a, bumpCube x a

private theorem locallyFinite_bumpCube :
    LocallyFinite (fun a : LatticeIndex => support (fun x => bumpCube x a)) := by
  refine locallyFinite_latticeClosedBall.subset fun a x hx => ?_
  by_contra hnot
  apply hx
  have hFar : ¬ x - latticeCenter a ∈ ball (0 : LatticeSpace) bump.rOut := by
    intro hIn
    apply hnot
    rw [mem_ball, dist_zero_right] at hIn
    rw [mem_closedBall, dist_eq_norm]
    exact hIn.le.trans (by norm_num [bump])
  have hZero : bump (x - latticeCenter a) = 0 := by
    apply notMem_support.mp
    rwa [bump.support_eq]
  simp [bumpCube, hZero]

private theorem cubeSum_positive (x : LatticeSpace) : 0 < cubeSum x := by
  obtain ⟨a, ha⟩ := mem_iUnion.mp
    (show x ∈ ⋃ a : LatticeIndex, ball (latticeCenter a) 3 by rw [lattice_ball_cover]; trivial)
  have hOne : bump (x - latticeCenter a) = 1 := by
    apply bump.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt (by simpa only [mem_ball, dist_eq_norm] using ha)
  have hF := locallyFinite_bumpCube.point_finite x
  have hPos : 0 < bumpCube x a := by simp [bumpCube, hOne]
  have hNonneg (j : LatticeIndex) : 0 ≤ bumpCube x j := pow_nonneg bump.nonneg _
  unfold cubeSum
  rw [finsum_eq_sum _ hF]
  exact hPos.trans_le (Finset.single_le_sum (fun j _ => hNonneg j)
    (hF.mem_toFinset.mpr hPos.ne'))

private theorem cubeSum_smooth : ContDiff ℝ ∞ cubeSum := by
  have h (a : LatticeIndex) : ContDiff ℝ ∞ (fun x => bumpCube x a) :=
    ((bump.contDiff : ContDiff ℝ ∞ (bump : LatticeSpace → ℝ)).comp
      (contDiff_id.sub contDiff_const)).pow 3
  exact (contMDiff_finsum (fun a => (h a).contMDiff) locallyFinite_bumpCube).contDiff

private theorem cubeSum_translate (x : LatticeSpace) (b : LatticeIndex) :
    cubeSum (x - latticeCenter b) = cubeSum x := by
  unfold cubeSum
  refine finsum_eq_of_bijective (fun a : LatticeIndex => a + b) (Equiv.addRight b).bijective ?_
  intro a
  simp only [bumpCube, latticeCenter_add]
  rw [sub_sub, add_comm (latticeCenter b)]

/-- A fixed compact smooth shape gives an exact cubic partition after
integer translation. The topological support is in radius four. -/
theorem exists_cubic_lattice_profile :
    ∃ q : LatticeSpace → ℝ, ContDiff ℝ ∞ q ∧ (∀ x, 0 ≤ q x) ∧
      tsupport q ⊆ closedBall 0 4 ∧
      ∀ x, (∑ᶠ a : LatticeIndex, q (x - latticeCenter a) ^ 3) = 1 := by
  let d (x : LatticeSpace) := cubeSum x ^ ((1 : ℝ) / 3)
  let q (x : LatticeSpace) := bump x / d x
  have hD (x : LatticeSpace) : 0 < d x := Real.rpow_pos_of_pos (cubeSum_positive x) _
  have hSmooth : ContDiff ℝ ∞ d := by
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    exact (Real.contDiffAt_rpow_const_of_ne (cubeSum_positive x).ne').comp x cubeSum_smooth.contDiffAt
  refine ⟨q, bump.contDiff.div hSmooth (fun x => (hD x).ne'), ?_, ?_, ?_⟩
  · exact fun x => div_nonneg bump.nonneg (hD x).le
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hb : x ∈ support (bump : LatticeSpace → ℝ) := by
      intro hb
      exact hx (by simp [q, hb])
    rw [bump.support_eq] at hb
    exact ball_subset_closedBall hb
  · intro x
    have hCube : d x ^ 3 = cubeSum x := by
      dsimp [d]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (cubeSum_positive x).le]
      norm_num
    calc
      _ = ∑ᶠ a : LatticeIndex, bumpCube x a / cubeSum x := by
        congr 1
        funext a
        simp only [q, div_pow, bumpCube, show d (x - latticeCenter a) = d x from by
          dsimp [d]; rw [cubeSum_translate], hCube]
      _ = cubeSum x / cubeSum x := by
        simp only [div_eq_mul_inv, finsum_mul, cubeSum]
      _ = 1 := div_self (cubeSum_positive x).ne'

end Burnett.C01
