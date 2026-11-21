import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderDyadic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Bornology Filter Set Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators ContDiff FourierTransform Topology

/-- The frequency derivative bounds for an order-one symbol. The full
Hörmander class also imposes the analogous bounds on all base derivatives. -/
structure FrequencyOrderOne (a : E → E → ℂ) : Prop where
  smooth : ∀ x, ContDiff ℝ ∞ (a x)
  order : ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ξ,
    ‖iteratedFDeriv ℝ n (a x) ξ‖ * (1 + ‖ξ‖) ^ n ≤ M * (1 + ‖ξ‖)

private theorem scale_le (j : ℕ) : 1 ≤ dyadicScale j := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

private theorem normalizeSlice_support (a : E → E → ℂ) (x : E) (j : ℕ) :
    tsupport (normalizedFirstOrderAnnulus a x j) ⊆ {z : E | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4} := by
  apply closure_minimal
  · intro z hz
    change 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 4
    constructor
    · by_contra! h
      exact hz (by simp [normalizedFirstOrderAnnulus, annulus_eq_zero_near z h.le])
    · by_contra! h
      exact hz (by simp [normalizedFirstOrderAnnulus, annulus_eq_zero_far z h.le])
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

private theorem normalizeSlice_smooth {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (x : E) (j : ℕ) : ContDiff ℝ ∞ (normalizedFirstOrderAnnulus a x j) := by
  unfold normalizedFirstOrderAnnulus
  exact ((Complex.ofRealCLM.contDiff.comp annulus_contDiff).mul
    ((ha.smooth x).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => dyadicScale j)).smul contDiff_id))).const_smul _

private def normalizedSlice {a : E → E → ℂ} (ha : FrequencyOrderOne a) (x : E) (j : ℕ) :
    SchwartzMap E ℂ := by
  have hC : HasCompactSupport (normalizedFirstOrderAnnulus a x j) :=
    (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure fun z hz =>
      Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (normalizeSlice_support a x j hz).2)
  exact hC.toSchwartzMap (normalizeSlice_smooth ha x j)

private theorem scaledRaw_iterated_le {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (n : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hOrder : ∀ x ξ, ‖iteratedFDeriv ℝ n (a x) ξ‖ * (1 + ‖ξ‖) ^ n ≤ M * (1 + ‖ξ‖))
    (x : E) (j : ℕ) (η : E) (hη₁ : 1 ≤ ‖η‖) (hη₄ : ‖η‖ ≤ 4) :
    ‖iteratedFDeriv ℝ n (fun z : E => (dyadicScale j)⁻¹ • a x (dyadicScale j • z)) η‖ ≤ 5 * M := by
  let s := dyadicScale j
  let T : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  have hs₁ : 1 ≤ s := scale_le j
  have hs : 0 < s := zero_lt_one.trans_le hs₁
  have hT (z : E) : T z = s • z := rfl
  have hTNorm : ‖T‖ ≤ s := by
    exact T.opNorm_le_bound hs.le (fun z => by rw [hT, norm_smul, Real.norm_of_nonneg hs.le])
  have hd : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hSmooth := (ha.smooth x).comp T.contDiff
  change ‖iteratedFDeriv ℝ n (s⁻¹ • (a x ∘ T)) η‖ ≤ 5 * M
  rw [iteratedFDeriv_const_smul_apply (hSmooth.contDiffAt.of_le hd), norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hs.le), T.iteratedFDeriv_comp_right (ha.smooth x) η hd]
  let W := 1 + ‖T η‖
  let A := ‖iteratedFDeriv ℝ n (a x) (T η)‖
  have hW : W = 1 + s * ‖η‖ := by
    change 1 + ‖T η‖ = _
    rw [hT, norm_smul, Real.norm_of_nonneg hs.le]
  have hWeights : s ≤ W ∧ W ≤ 5 * s := by
    rw [hW]
    constructor
    · linarith [mul_le_mul_of_nonneg_left hη₁ hs.le]
    · linarith [mul_le_mul_of_nonneg_left hη₄ hs.le]
  exact calc
    _ ≤ s⁻¹ * (A * ‖T‖ ^ n) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
      simpa only [A, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ n (a x) (T η)) (fun _ => T))
    _ ≤ s⁻¹ * (A * W ^ n) := by gcongr; exact hTNorm.trans hWeights.1
    _ ≤ s⁻¹ * (M * W) := mul_le_mul_of_nonneg_left (hOrder x (T η)) (inv_nonneg.mpr hs.le)
    _ ≤ s⁻¹ * (M * (5 * s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeights.2 hM) (inv_nonneg.mpr hs.le)
    _ = 5 * M := by field_simp

private theorem normalizedSlices_bounded {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    IsVonNBounded ℝ (Set.range (fun p : E × ℕ => normalizedSlice ha p.1 p.2)) := by
  classical
  rw [← image_univ]
  apply ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded _).mpr
  intro kn
  obtain ⟨k,n⟩ := kn
  choose M hM hOrder using ha.order
  have hCutoff : HasCompactSupport (fun z : E => (annulus z : ℂ)) := by
    apply (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    by_contra hn
    have hn' : 4 < ‖z‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn)
    exact hz (by simp [annulus_eq_zero_far z hn'.le])
  let cutoff := hCutoff.toSchwartzMap (Complex.ofRealCLM.contDiff.comp annulus_contDiff)
  let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i cutoff * (5 * M (n-i))
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (mul_nonneg (by norm_num) (hM _))
  refine ⟨4 ^ k * C + 1, by positivity, ?_⟩
  rintro ⟨x,j⟩ _
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (normalizedSlice ha x j) (by positivity) ?_)
    (lt_add_one _)
  intro η
  by_cases hη : η ∈ tsupport (normalizedFirstOrderAnnulus a x j)
  · obtain ⟨hη₁,hη₄⟩ := normalizeSlice_support a x j hη
    let g (z : E) := (dyadicScale j)⁻¹ • a x (dyadicScale j • z)
    have hg : ContDiff ℝ ∞ g :=
      ((ha.smooth x).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => dyadicScale j)).smul contDiff_id)).const_smul _
    have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hEq : (normalizedSlice ha x j : E → ℂ) = fun z => cutoff z * g z := by
      funext z
      change (dyadicScale j)⁻¹ • (annulus z : ℂ) • a x (dyadicScale j • z) =
        (annulus z : ℂ) • (dyadicScale j)⁻¹ • a x (dyadicScale j • z)
      exact smul_comm (dyadicScale j)⁻¹ (annulus z : ℂ) (a x (dyadicScale j • z))
    rw [hEq]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hη₄ _) ?_ (norm_nonneg _) (by positivity)
    apply (norm_iteratedFDeriv_mul_le cutoff.smooth' hg η hn).trans
    apply Finset.sum_le_sum
    intro i _
    have hi : ‖iteratedFDeriv ℝ i (cutoff : E → ℂ) η‖ ≤ SchwartzMap.seminorm ℝ 0 i cutoff := by
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 i cutoff η
    exact mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _))
      (scaledRaw_iterated_le ha _ _ (hM _) (hOrder _) x j η hη₁ hη₄) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
  · have hD : iteratedFDeriv ℝ n (normalizedSlice ha x j : E → ℂ) η = 0 := by
      by_contra hD
      exact hη (support_iteratedFDeriv_subset n hD)
    simpa only [hD, norm_zero, mul_zero] using (mul_nonneg (by positivity : 0 ≤ (4 : ℝ)^k) hC)

/-- The ordinary frequency derivative bounds construct the uniformly bounded
profiles that the actual dyadic kernel estimate consumes. -/
theorem exists_normalizedInverseProfiles {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ (p : E → ℕ → SchwartzMap E ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ x j, (p x j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j)) ∧
      (∀ x j, SchwartzMap.seminorm ℝ 0 0 (p x j) ≤ C ∧ SchwartzMap.seminorm ℝ 6 0 (p x j) ≤ C) := by
  let F := (SchwartzMap.fourierTransformCLE ℝ (V := E) (E := ℂ)).symm
  let p (x : E) (j : ℕ) := F (normalizedSlice ha x j)
  have hP : IsVonNBounded ℝ (Set.range fun q : E × ℕ => p q.1 q.2) := by
    have h := (normalizedSlices_bounded ha).image F.toContinuousLinearMap
    rwa [← Set.range_comp] at h
  rw [← image_univ] at hP
  have hB := ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded _).mp hP
  obtain ⟨L,hL,hL'⟩ := hB (0,0)
  obtain ⟨S,hS,hS'⟩ := hB (6,0)
  refine ⟨p, max L S, hL.le.trans (le_max_left _ _), ?_, ?_⟩
  · intro x j
    funext z
    simp only [p, F, SchwartzMap.fourierTransformCLE_symm_apply]
    rfl
  · intro x j
    exact ⟨(hL' (x,j) trivial).le.trans (le_max_left _ _), (hS' (x,j) trivial).le.trans (le_max_right _ _)⟩

/-- The inverse annulus family remains bounded after arbitrary fixed
Schwartz-space operations such as differentiation. -/
theorem exists_boundedInverseProfiles {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ p : E → ℕ → SchwartzMap E ℂ,
      (∀ x j, (p x j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j)) ∧
      IsVonNBounded ℝ (Set.range fun q : E × ℕ => p q.1 q.2) := by
  let F := (SchwartzMap.fourierTransformCLE ℝ (V := E) (E := ℂ)).symm
  let p (x : E) (j : ℕ) := F (normalizedSlice ha x j)
  refine ⟨p, ?_, ?_⟩
  · intro x j
    funext z
    simp only [p, F, SchwartzMap.fourierTransformCLE_symm_apply]
    rfl
  · have h := (normalizedSlices_bounded ha).image F.toContinuousLinearMap
    rwa [← Set.range_comp] at h

/-- A uniformly controlled family of frequency symbols can use an arbitrary
index set, independently of the spatial type of the quantization. -/
theorem exists_uniformFamilyInverseProfiles {I : Type*} (f : I → E → ℂ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (f i))
    (horder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ξ,
      ‖iteratedFDeriv ℝ n (f i) ξ‖ * (1 + ‖ξ‖) ^ n ≤ C * (1 + ‖ξ‖)) :
    ∃ (p : I → ℕ → SchwartzMap E ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ i j, (p i j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus (fun _ => f i) 0 j)) ∧
      (∀ i j, SchwartzMap.seminorm ℝ 6 0 (p i j) ≤ C) := by
  classical
  choose A hA hOrder using horder
  have hF (i : I) : FrequencyOrderOne (fun _ => f i) :=
    ⟨fun _ => hsmooth i, fun n => ⟨A n, hA n, fun _ ξ => hOrder n i ξ⟩⟩
  let q (ij : I × ℕ) : SchwartzMap E ℂ := normalizedSlice (hF ij.1) 0 ij.2
  have hq : IsVonNBounded ℝ (q '' univ) := by
    apply ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded q).mpr
    rintro ⟨k,n⟩
    have hCutoff : HasCompactSupport (fun z : E => (annulus z : ℂ)) := by
      apply (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure
      apply closure_minimal _ Metric.isClosed_closedBall
      intro z hz
      by_contra hZ
      have hFar : 4 < ‖z‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hZ)
      exact hz (by simp [annulus_eq_zero_far z hFar.le])
    let c := hCutoff.toSchwartzMap (Complex.ofRealCLM.contDiff.comp annulus_contDiff)
    let M := ∑ m ∈ Finset.range (n+1), (n.choose m : ℝ) * SchwartzMap.seminorm ℝ 0 m c * (5 * A (n-m))
    have hM : 0 ≤ M := Finset.sum_nonneg fun m _ => by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (mul_nonneg (by norm_num) (hA _))
    refine ⟨4 ^ k * M + 1, by positivity, ?_⟩
    rintro ⟨i,j⟩ _
    apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (q (i,j)) (by positivity) ?_) (lt_add_one _)
    intro η
    by_cases hη : η ∈ tsupport (normalizedFirstOrderAnnulus (fun _ => f i) 0 j)
    · obtain ⟨ha,hb⟩ := normalizeSlice_support (fun _ => f i) 0 j hη
      let g (z : E) := (dyadicScale j)⁻¹ • f i (dyadicScale j • z)
      have hg : ContDiff ℝ ∞ g :=
        ((hsmooth i).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => dyadicScale j)).smul contDiff_id)).const_smul _
      have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      have hEq : (q (i,j) : E → ℂ) = fun z => c z * g z := by
        funext z
        change (dyadicScale j)⁻¹ • (annulus z : ℂ) • f i (dyadicScale j • z) =
          (annulus z : ℂ) • (dyadicScale j)⁻¹ • f i (dyadicScale j • z)
        exact smul_comm (dyadicScale j)⁻¹ (annulus z : ℂ) (f i (dyadicScale j • z))
      rw [hEq]
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb _) ?_ (norm_nonneg _) (by positivity)
      apply (norm_iteratedFDeriv_mul_le c.smooth' hg η hn).trans
      apply Finset.sum_le_sum
      intro m _
      have hi : ‖iteratedFDeriv ℝ m (c : E → ℂ) η‖ ≤ SchwartzMap.seminorm ℝ 0 m c := by
        simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 m c η
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _))
        (scaledRaw_iterated_le (hF i) _ _ (hA _) (fun _ ξ => hOrder _ i ξ) 0 j η ha hb)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    · have hd : iteratedFDeriv ℝ n (q (i,j) : E → ℂ) η = 0 := by
        by_contra hd
        exact hη (support_iteratedFDeriv_subset n hd)
      simpa only [hd, norm_zero, mul_zero] using (mul_nonneg (by positivity : 0 ≤ (4 : ℝ)^k) hM)
  let F := (SchwartzMap.fourierTransformCLE ℝ (V := E) (E := ℂ)).symm
  have hP : IsVonNBounded ℝ ((fun v : I × ℕ => F (q v)) '' univ) := by
    simpa only [image_image] using hq.image F.toContinuousLinearMap
  have hB := ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded _).mp hP
  obtain ⟨C,hC,hC'⟩ := hB (6,0)
  refine ⟨fun i j => F (q (i,j)), C, hC.le, ?_, fun i j => (hC' (i,j) trivial).le⟩
  intro i j
  funext z
  simp only [F, SchwartzMap.fourierTransformCLE_symm_apply]
  rfl

end Burnett.Analysis.FirstOrderDyadic
