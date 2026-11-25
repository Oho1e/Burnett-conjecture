import Burnett.Analysis.TransportPatches.CubicPartitionProfile
import Mathlib.Topology.MetricSpace.Thickening

/-! Cubed cutoffs on each fixed localization scale, with nested plateaus
and uniform derivative constants from two fixed smooth profiles. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.C01

open Set Function Filter Metric Burnett.Analysis.CarlesonEmbedding
open scoped ContDiff Manifold BigOperators Topology

def patchCenter (ℓ : ℝ) (a : LatticeIndex) : LatticeSpace := ℓ • latticeCenter a

private def patchCoordinate (ℓ : ℝ) (a : LatticeIndex) (x : LatticeSpace) : LatticeSpace :=
  ℓ⁻¹ • x - latticeCenter a

private theorem dist_patchCenter (ℓ : ℝ) (hℓ : 0 < ℓ) (a : LatticeIndex) (x : LatticeSpace) :
    dist x (patchCenter ℓ a) = ℓ * ‖patchCoordinate ℓ a x‖ := by
  have h : ℓ • patchCoordinate ℓ a x = x - patchCenter ℓ a := by
    simp only [patchCoordinate, patchCenter, smul_sub, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  rw [dist_eq_norm, ← h, norm_smul, Real.norm_of_nonneg hℓ.le]

private theorem mem_patchBall_iff (ℓ : ℝ) (hℓ : 0 < ℓ) (a : LatticeIndex) (x : LatticeSpace) (R : ℝ) :
    x ∈ closedBall (patchCenter ℓ a) (R * ℓ) ↔ ‖patchCoordinate ℓ a x‖ ≤ R := by
  rw [mem_closedBall, dist_patchCenter ℓ hℓ, mul_comm R ℓ, mul_le_mul_iff_right₀ hℓ]

private theorem locallyFinite_patchBall (ℓ : ℝ) (hℓ : 0 < ℓ) {R : ℝ} (hR : R ≤ 6) :
    LocallyFinite (fun a : LatticeIndex => closedBall (patchCenter ℓ a) (R * ℓ)) := by
  have hf : Continuous (fun x : LatticeSpace => ℓ⁻¹ • x) := continuous_const.smul continuous_id
  refine (locallyFinite_latticeClosedBall.preimage_continuous hf).subset fun a x hx => ?_
  change dist (ℓ⁻¹ • x) (latticeCenter a) ≤ 6
  rw [dist_eq_norm]
  exact ((mem_patchBall_iff ℓ hℓ a x R).mp hx).trans hR

private theorem tsupport_scaledProfile (q : LatticeSpace → ℝ) {R : ℝ}
    (hSupp : tsupport q ⊆ closedBall 0 R) (ℓ : ℝ) (hℓ : 0 < ℓ) (a : LatticeIndex) :
    tsupport (q ∘ patchCoordinate ℓ a) ⊆ closedBall (patchCenter ℓ a) (R * ℓ) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  apply (mem_patchBall_iff ℓ hℓ a x R).mpr
  have h := hSupp (subset_closure (show patchCoordinate ℓ a x ∈ support q from hx))
  simpa only [mem_closedBall, dist_zero_right] using h

private theorem norm_iteratedFDeriv_scaledProfile (q : SchwartzMap LatticeSpace ℝ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (a : LatticeIndex) (x : LatticeSpace) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (q ∘ patchCoordinate ℓ a) x‖ ≤
      SchwartzMap.seminorm ℝ 0 k q * ℓ⁻¹ ^ k := by
  let L : LatticeSpace →L[ℝ] LatticeSpace := ℓ⁻¹ • ContinuousLinearMap.id ℝ LatticeSpace
  let d := -latticeCenter a
  let v (y : LatticeSpace) := q (y + d)
  have hv : ContDiff ℝ ∞ v := (q.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hF : q ∘ patchCoordinate ℓ a = v ∘ L := by
    funext y
    simp [v, L, d, patchCoordinate, sub_eq_add_neg]
  have hk : (k : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hNorm : ‖L‖ = ℓ⁻¹ := by
    simp [L, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), ContinuousLinearMap.norm_id]
  rw [hF, L.iteratedFDeriv_comp_right hv x hk]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k v (L x)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k q (L x + d)‖ * ℓ⁻¹ ^ k := by
      change ‖iteratedFDeriv ℝ k (fun y => q (y + d)) (L x)‖ * _ = _
      rw [iteratedFDeriv_comp_add_right, hNorm]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ q k _)
      (pow_nonneg (inv_nonneg.mpr hℓ.le) _)

/-- Finite cube partition on a neighborhood of a compact set. The outer
0-to-1 bump is identically one on the open scale-`ℓ` neighborhood of the
inner support and remains inside the prescribed compact-base window. -/
theorem exists_scaled_cubic_cutoffs {K Kplus : Set LatticeSpace}
    (hK : IsCompact K) (hNested : K ⊆ interior Kplus) :
    ∃ (ℓ₀ : ℝ) (C : ℕ → ℝ), 0 < ℓ₀ ∧ (∀ k, 0 ≤ C k) ∧
      ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
        ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → LatticeSpace → ℝ),
          (∀ x ∈ thickening ℓ K, (∑ a ∈ s, χ a x ^ 3) = 1) ∧
          (∀ a ∈ s, ContDiff ℝ ∞ (χ a) ∧ ContDiff ℝ ∞ (χplus a) ∧
            (∀ x, 0 ≤ χ a x ∧ χplus a x ∈ Icc (0 : ℝ) 1) ∧
            tsupport (χ a) ⊆ closedBall (patchCenter ℓ a) (4 * ℓ) ∧
            tsupport (χplus a) ⊆ closedBall (patchCenter ℓ a) (6 * ℓ) ∧
            closedBall (patchCenter ℓ a) (6 * ℓ) ⊆ Kplus ∧
            (∀ x ∈ thickening ℓ (tsupport (χ a)), χplus a x = 1) ∧
            ∀ k x, ‖iteratedFDeriv ℝ k (χ a) x‖ ≤ C k * ℓ⁻¹ ^ k ∧
              ‖iteratedFDeriv ℝ k (χplus a) x‖ ≤ C k * ℓ⁻¹ ^ k) := by
  classical
  obtain ⟨δ, hδ, hMargin⟩ := hK.exists_cthickening_subset_open isOpen_interior hNested
  obtain ⟨q, hq, hNonneg, hSupport, hPartition⟩ := exists_cubic_lattice_profile
  let g : ContDiffBump (0 : LatticeSpace) := ⟨5, 6, by norm_num, by norm_num⟩
  have hgSupport : tsupport (g : LatticeSpace → ℝ) ⊆ closedBall 0 6 :=
    g.tsupport_eq ▸ subset_rfl
  have hCompact : HasCompactSupport q :=
    (isCompact_closedBall 0 4).of_isClosed_subset isClosed_closure hSupport
  let f : SchwartzMap LatticeSpace ℝ := hCompact.toSchwartzMap hq
  let fplus : SchwartzMap LatticeSpace ℝ := g.hasCompactSupport.toSchwartzMap g.contDiff
  let C (k : ℕ) := SchwartzMap.seminorm ℝ 0 k f + SchwartzMap.seminorm ℝ 0 k fplus
  refine ⟨δ / 12, C, by positivity, fun k => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _), ?_⟩
  intro ℓ hℓ hSmall
  let W := cthickening ℓ K
  let S := {a : LatticeIndex | (closedBall (patchCenter ℓ a) (4 * ℓ) ∩ W).Nonempty}
  have hLocal := locallyFinite_patchBall ℓ hℓ (R := 4) (by norm_num)
  have hS : S.Finite := hLocal.finite_nonempty_inter_compact (hK.cthickening (r := ℓ))
  let s := hS.toFinset
  let χ (a : LatticeIndex) := q ∘ patchCoordinate ℓ a
  let χplus (a : LatticeIndex) := (g : LatticeSpace → ℝ) ∘ patchCoordinate ℓ a
  refine ⟨s, χ, χplus, ?_, ?_⟩
  · intro x hx
    have hEq : (∑ᶠ a : LatticeIndex, χ a x ^ 3) = 1 := hPartition (ℓ⁻¹ • x)
    rw [← hEq]
    symm
    refine finsum_eq_sum_of_support_subset _ ?_
    intro a ha
    have hxq : x ∈ support (χ a) := by
      intro hz
      apply ha
      change χ a x ^ 3 = 0
      rw [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)]
    have hBall := tsupport_scaledProfile q hSupport ℓ hℓ a (subset_closure hxq)
    exact hS.mem_toFinset.mpr ⟨x, hBall, thickening_subset_cthickening ℓ K hx⟩
  · intro a ha
    have hχ := tsupport_scaledProfile q hSupport ℓ hℓ a
    have hχplus := tsupport_scaledProfile (g : LatticeSpace → ℝ) hgSupport ℓ hℓ a
    have hCoord : ContDiff ℝ ∞ (patchCoordinate ℓ a) :=
      (contDiff_const.smul contDiff_id).sub contDiff_const
    refine ⟨hq.comp hCoord, g.contDiff.comp hCoord, fun x => ⟨hNonneg _, g.nonneg, g.le_one⟩,
      hχ, hχplus, ?_, ?_, ?_⟩
    · obtain ⟨y, hyInner, hyWide⟩ := hS.mem_toFinset.mp ha
      change y ∈ cthickening ℓ K at hyWide
      rw [hK.cthickening_eq_biUnion_closedBall hℓ.le, Set.mem_iUnion₂] at hyWide
      obtain ⟨z, hz, hyz⟩ := hyWide
      intro x hx
      have hxy : dist x y ≤ 10 * ℓ := by
        have h₁ : dist x (patchCenter ℓ a) ≤ 6 * ℓ := hx
        have h₂ : dist (patchCenter ℓ a) y ≤ 4 * ℓ := dist_comm y _ ▸ hyInner
        linarith [dist_triangle x (patchCenter ℓ a) y]
      have hDist : dist x z ≤ δ := by
        have h₃ : dist y z ≤ ℓ := hyz
        linarith [dist_triangle x y z]
      exact interior_subset (hMargin (by
        rw [hK.cthickening_eq_biUnion_closedBall hδ.le, Set.mem_iUnion₂]
        exact ⟨z, hz, hDist⟩))
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
      have hyDist : dist y (patchCenter ℓ a) ≤ 4 * ℓ := hχ hy
      have hxDist : dist x (patchCenter ℓ a) ≤ 5 * ℓ := by
        linarith [dist_triangle x y (patchCenter ℓ a)]
      have hIn := (mem_patchBall_iff ℓ hℓ a x 5).mp hxDist
      apply g.one_of_mem_closedBall
      simpa only [mem_closedBall, dist_zero_right] using hIn
    · intro k x
      have hPow : 0 ≤ ℓ⁻¹ ^ k := pow_nonneg (inv_nonneg.mpr hℓ.le) _
      exact ⟨(norm_iteratedFDeriv_scaledProfile f ℓ hℓ a x k).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) hPow),
        (norm_iteratedFDeriv_scaledProfile fplus ℓ hℓ a x k).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) hPow)⟩

end Burnett.C01
