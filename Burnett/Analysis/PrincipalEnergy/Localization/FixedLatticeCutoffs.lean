import Burnett.Analysis.PrincipalEnergy.Localization.FixedLatticeGeometry
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Set Function Metric
open scoped BigOperators ComplexConjugate ContDiff Manifold

/-- The same Schwartz partition on the integer lattice supplies finite
subpartitions adapted to arbitrary compact data. -/
theorem exists_lattice_schwartz_subpartition :
    ∃ α : LatticeIndex → SchwartzMap LatticeSpace ℂ,
      (∀ a, tsupport (α a : LatticeSpace → ℂ) ⊆ closedBall (latticeCenter a) 3) ∧
      (∀ a x, α a x = ((α a x).re : ℂ)) ∧ (∀ a x, 0 ≤ (α a x).re) ∧
      ∀ K : Set LatticeSpace, IsCompact K → ∃ s : Finset LatticeIndex,
        (∀ x, (∑ a ∈ s, (α a x).re) ≤ 1) ∧ (∀ x ∈ K, ∑ a ∈ s, α a x = 1) := by
  classical
  let U (a : LatticeIndex) := ball (latticeCenter a) 3
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, LatticeSpace)) (s := (univ : Set LatticeSpace)) isClosed_univ U
    (fun _ => isOpen_ball) (by rw [show (⋃ a, U a) = univ from lattice_ball_cover])
  let f (a : LatticeIndex) (x : LatticeSpace) := (ρ a x : ℂ)
  have same (a : LatticeIndex) : tsupport (f a) = tsupport (ρ a) := by
    change closure (support (f a)) = closure (support (ρ a))
    apply congrArg closure
    ext x
    change (↑(ρ a x) : ℂ) ≠ 0 ↔ ρ a x ≠ 0
    simp
  have inside (a : LatticeIndex) : tsupport (f a) ⊆ closedBall (latticeCenter a) 3 := by
    rw [same]
    exact (hρ a).trans ball_subset_closedBall
  have compactSupp (a : LatticeIndex) : HasCompactSupport (f a) :=
    (isCompact_closedBall (latticeCenter a) 3).of_isClosed_subset isClosed_closure (inside a)
  let α (a : LatticeIndex) : SchwartzMap LatticeSpace ℂ :=
    (compactSupp a).toSchwartzMap (Complex.ofRealCLM.contDiff.comp (ρ a).contMDiff.contDiff)
  refine ⟨α, inside, fun a x => ?_, fun a x => ?_, ?_⟩
  · change (↑(ρ a x) : ℂ) = (↑((↑(ρ a x) : ℂ).re) : ℂ)
    rw [Complex.ofReal_re]
  · change 0 ≤ ((ρ a x : ℝ) : ℂ).re
    simpa only [Complex.ofReal_re] using ρ.nonneg a x
  intro K hK
  let S := {a : LatticeIndex | (support (ρ a) ∩ K).Nonempty}
  have hS : S.Finite := ρ.locallyFinite.finite_nonempty_inter_compact hK
  let s := hS.toFinset
  have hs {a : LatticeIndex} (ha : a ∈ S) : a ∈ s := hS.mem_toFinset.mpr ha
  refine ⟨s, ?_, ?_⟩
  · intro x
    change (∑ a ∈ s, ((ρ a x : ℝ) : ℂ).re) ≤ 1
    simp only [Complex.ofReal_re]
    calc
      _ = ∑ a ∈ s ∩ ρ.finsupport x, ρ a x := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro a ha hn
        have hzero : a ∉ ρ.finsupport x := fun h => hn (Finset.mem_inter.mpr ⟨ha, h⟩)
        exact notMem_support.mp (mt (ρ.mem_finsupport x).2 hzero)
      _ ≤ ∑ a ∈ ρ.finsupport x, ρ a x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun a _ _ => ρ.nonneg a x)
      _ = 1 := ρ.sum_finsupport x (mem_univ x)
  · intro x hx
    have hsubset : ρ.finsupport x ⊆ s := by
      intro a ha
      exact hs ⟨x, (ρ.mem_finsupport x).mp ha, hx⟩
    change (∑ a ∈ s, ((ρ a x : ℝ) : ℂ)) = 1
    exact_mod_cast (ρ.sum_finsupport' x (mem_univ x) hsubset)

/-- One real Schwartz plateau works at every lattice center by translation. -/
theorem exists_lattice_schwartz_plateau :
    ∃ χ : SchwartzMap LatticeSpace ℂ, HasCompactSupport (χ : LatticeSpace → ℂ) ∧
      (∀ x, conj (χ x) = χ x) ∧ ∀ x : LatticeSpace, ‖x‖ ≤ 19 → χ x = 1 := by
  let g : ContDiffBump (0 : LatticeSpace) := ⟨19, 20, by norm_num, by norm_num⟩
  let f (x : LatticeSpace) := (g x : ℂ)
  have hs : support f = support (g : LatticeSpace → ℝ) := by
    ext x
    simp [f, mem_support]
  have hc : HasCompactSupport f := by
    unfold HasCompactSupport tsupport
    rw [hs]
    exact g.hasCompactSupport
  let χ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp g.contDiff)
  refine ⟨χ, hc, fun _ => Complex.conj_ofReal _, ?_⟩
  intro x hx
  change (g x : ℂ) = 1
  rw [g.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hx)]
  exact Complex.ofReal_one

end Burnett.Analysis.CarlesonEmbedding
