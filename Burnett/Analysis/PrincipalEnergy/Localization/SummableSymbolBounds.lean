import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauMatrix
import Burnett.Analysis.PrincipalEnergy.Localization.LocallySummableJets

set_option autoImplicit false
set_option maxHeartbeats 6200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function Metric Set
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff Topology

/-- The shared base support and the shared derivative bounds used by the
compact-base commutator for a symbol family. -/
structure UniformCompactSymbolFamily {ι : Type*} (a : ι → Space → Space → ℂ) : Prop where
  support : ∃ K : Set Space, IsCompact K ∧ ∀ i ξ, tsupport (fun x => a i x ξ) ⊆ K
  smoothFrequency : ∀ i x, ContDiff ℝ ∞ (a i x)
  smoothBase : ∀ i ξ, ContDiff ℝ ∞ (fun x => a i x ξ)
  jointlyContinuous : ∀ i, Continuous (uncurry (a i))
  differentiableMixed : ∀ i (n : ℕ) ξ, Differentiable ℝ (fun x => iteratedFDeriv ℝ n (a i x) ξ)
  frequencyOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x ξ,
    ‖iteratedFDeriv ℝ n (a i x) ξ‖ * (1 + ‖ξ‖)^n ≤ C * (1 + ‖ξ‖)
  pureBaseOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x ξ,
    ‖iteratedFDeriv ℝ n (fun y => a i y ξ) x‖ ≤ C * (1 + ‖ξ‖)
  mixedOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x ξ,
    ‖fderiv ℝ (fun y => iteratedFDeriv ℝ n (a i y) ξ) x‖ * (1 + ‖ξ‖)^n ≤ C * (1 + ‖ξ‖)

/-- A real absolutely summable superposition of symbols. -/
def summableSymbolSum (a : ℕ → Space → Space → ℂ) (u : ℕ → ℝ) (x ξ : Space) : ℂ :=
  ∑' i, u i • a i x ξ

private theorem weightedTsum_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖)) {f : ℕ → F} {C : ℝ}
    (h : ∀ i, ‖f i‖ ≤ C) : ‖∑' i, u i • f i‖ ≤ (∑' i, ‖u i‖) * C := by
  have hm := hu.mul_right C
  have hb (i : ℕ) : ‖u i • f i‖ ≤ ‖u i‖ * C := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
  have hs : Summable (fun i => ‖u i • f i‖) := .of_nonneg_of_le (fun _ => norm_nonneg _) hb hm
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb hm).trans_eq (hu.tsum_mul_right C))

private theorem norm_iteratedFDeriv_const_real_smul {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (u : ℝ) (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (fun y => u • f y) x = u • iteratedFDeriv ℝ n f x :=
  iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by exact_mod_cast le_top))

private theorem one_add_norm_le_of_mem_ball {x y : Space} (hy : y ∈ ball x 1) :
    1 + ‖y‖ ≤ 2 + ‖x‖ := by
  have h : ‖y-x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
  have hNorm : ‖y‖ ≤ ‖y-x‖ + ‖x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y-x) x
  linarith only [h, hNorm]

private theorem summableSymbolSum_frequency_jets {a : ℕ → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖)) (x : Space) :
    ContDiff ℝ ∞ (summableSymbolSum a u x) ∧ ∀ (n : ℕ) ξ,
      iteratedFDeriv ℝ n (summableSymbolSum a u x) ξ = ∑' i, u i • iteratedFDeriv ℝ n (a i x) ξ := by
  have hv (n : ℕ) (ξ : Space) : ∃ v : ℕ → ℝ, Summable v ∧ ∀ i η, η ∈ ball ξ 1 →
      ‖iteratedFDeriv ℝ n (fun ζ => u i • a i x ζ) η‖ ≤ v i := by
    obtain ⟨C, hC, hb⟩ := ha.frequencyOrder n
    refine ⟨fun i => ‖u i‖ * (C * (2 + ‖ξ‖)), hu.mul_right _, fun i η hη => ?_⟩
    rw [norm_iteratedFDeriv_const_real_smul (ha.smoothFrequency i x), norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hW : 1 ≤ (1 + ‖η‖)^n := one_le_pow₀ (by simp)
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (a i x) η‖ * (1 + ‖η‖)^n := le_mul_of_one_le_right (norm_nonneg _) hW
      _ ≤ C * (1 + ‖η‖) := hb i x η
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_add_norm_le_of_mem_ball hη) hC
  obtain ⟨hs, hj⟩ := contDiff_tsum_and_jets_of_locally_summable_bounds
    (fun i ξ => u i • a i x ξ) (fun i => (ha.smoothFrequency i x).const_smul _) hv
  exact ⟨hs, fun n ξ => (hj n ξ).trans (tsum_congr fun i =>
    norm_iteratedFDeriv_const_real_smul (ha.smoothFrequency i x) (u i) n ξ)⟩

private theorem summableSymbolSum_base_jets {a : ℕ → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖)) (ξ : Space) :
    ContDiff ℝ ∞ (fun x => summableSymbolSum a u x ξ) ∧ ∀ (n : ℕ) x,
      iteratedFDeriv ℝ n (fun y => summableSymbolSum a u y ξ) x =
        ∑' i, u i • iteratedFDeriv ℝ n (fun y => a i y ξ) x := by
  have hv (n : ℕ) (x : Space) : ∃ v : ℕ → ℝ, Summable v ∧ ∀ i y, y ∈ ball x 1 →
      ‖iteratedFDeriv ℝ n (fun z => u i • a i z ξ) y‖ ≤ v i := by
    obtain ⟨C, _, hb⟩ := ha.pureBaseOrder n
    refine ⟨fun i => ‖u i‖ * (C * (1 + ‖ξ‖)), hu.mul_right _, fun i y _ => ?_⟩
    rw [norm_iteratedFDeriv_const_real_smul (ha.smoothBase i ξ), norm_smul]
    exact mul_le_mul_of_nonneg_left (hb i y ξ) (norm_nonneg _)
  obtain ⟨hs, hj⟩ := contDiff_tsum_and_jets_of_locally_summable_bounds
    (fun i x => u i • a i x ξ) (fun i => (ha.smoothBase i ξ).const_smul _) hv
  exact ⟨hs, fun n x => (hj n x).trans (tsum_congr fun i =>
    norm_iteratedFDeriv_const_real_smul (ha.smoothBase i ξ) (u i) n x)⟩

private theorem summableSymbolSum_mixed_fderiv {a : ℕ → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖))
    (n : ℕ) (x ξ : Space) :
    HasFDerivAt (fun y => iteratedFDeriv ℝ n (summableSymbolSum a u y) ξ)
      (∑' i, u i • fderiv ℝ (fun y => iteratedFDeriv ℝ n (a i y) ξ) x) x := by
  let V := ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ
  letI : NormedAddCommGroup (Space →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Space →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
  obtain ⟨A, _, hA⟩ := ha.frequencyOrder n
  obtain ⟨B, _, hB⟩ := ha.mixedOrder n
  let W := 1 + ‖ξ‖
  have hW : 0 < W := by dsimp [W]; positivity
  let j (i : ℕ) (y : Space) := iteratedFDeriv ℝ n (a i y) ξ
  have hj (i : ℕ) (y : Space) : HasFDerivAt (j i) (fderiv ℝ (j i) y) y :=
    ((ha.differentiableMixed i n ξ) y).hasFDerivAt
  have hi : Summable (fun i => u i • j i 0) := by
    refine .of_norm_bounded (hu.mul_right (A * W / W^n)) fun i => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos hW _)).mpr (hA i 0 ξ)) (norm_nonneg _)
  have he (i : ℕ) (y : Space) : ‖u i • fderiv ℝ (j i) y‖ ≤ ‖u i‖ * (B * W / W^n) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos hW _)).mpr (hB i y ξ)) (norm_nonneg _)
  rw [show (fun y => iteratedFDeriv ℝ n (summableSymbolSum a u y) ξ) =
      (fun y => ∑' i, u i • j i y) from funext fun y => (summableSymbolSum_frequency_jets ha hu y).2 n ξ]
  exact hasFDerivAt_tsum (hu.mul_right _) (fun i y => (hj i y).const_smul (u i)) he hi x

/-- An absolutely summable superposition preserves the compact-base symbol
subclass and the first mixed derivatives used in the commutator theorem. -/
theorem summableSymbolSum_compactBase_inputs {a : ℕ → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖)) :
    FirstBaseFrequencyOrderOne (summableSymbolSum a u) ∧
    CompactBaseOrderOne (summableSymbolSum a u) ∧ Continuous (uncurry (summableSymbolSum a u)) := by
  let H := ∑' i, ‖u i‖
  have hH : 0 ≤ H := tsum_nonneg (fun _ => norm_nonneg _)
  have hSupport : ∃ K : Set Space, IsCompact K ∧ ∀ ξ,
      tsupport (fun x => summableSymbolSum a u x ξ) ⊆ K := by
    obtain ⟨K, hK, h⟩ := ha.support
    refine ⟨K, hK, fun ξ => closure_minimal (fun x hx => ?_) hK.isClosed⟩
    by_contra ho
    have hz (i : ℕ) : a i x ξ = 0 := by
      by_contra hne
      exact ho (h i ξ (subset_closure hne))
    exact hx (by simp only [summableSymbolSum, hz, smul_zero, tsum_zero])
  have hFreq : FrequencyOrderOne (summableSymbolSum a u) := by
    refine ⟨fun x => (summableSymbolSum_frequency_jets ha hu x).1, fun n => ?_⟩
    obtain ⟨C, hC, hb⟩ := ha.frequencyOrder n
    refine ⟨H * C, mul_nonneg hH hC, fun x ξ => ?_⟩
    let W := 1 + ‖ξ‖
    have hW : 0 < W := by dsimp [W]; positivity
    rw [(summableSymbolSum_frequency_jets ha hu x).2]
    calc
      _ ≤ (H * (C * W / W^n)) * W^n := mul_le_mul_of_nonneg_right
        (weightedTsum_bound hu (fun i => (le_div_iff₀ (pow_pos hW _)).mpr (hb i x ξ))) (by positivity)
      _ = H * C * W := by field_simp
  refine ⟨⟨hFreq, fun n ξ x => (summableSymbolSum_mixed_fderiv ha hu n x ξ).differentiableAt, ?_⟩,
    ⟨hSupport, fun ξ => (summableSymbolSum_base_jets ha hu ξ).1, ?_⟩, ?_⟩
  · intro n
    let V := ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ
    letI : NormedAddCommGroup (Space →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (Space →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
    obtain ⟨C, hC, hb⟩ := ha.mixedOrder n
    refine ⟨H * C, mul_nonneg hH hC, fun x ξ => ?_⟩
    let W := 1 + ‖ξ‖
    have hW : 0 < W := by dsimp [W]; positivity
    rw [(summableSymbolSum_mixed_fderiv ha hu n x ξ).fderiv]
    let d (i : ℕ) : Space →L[ℝ] V := fderiv ℝ (fun y => iteratedFDeriv ℝ n (a i y) ξ) x
    have hd (i : ℕ) : ‖d i‖ ≤ C * W / W^n := (le_div_iff₀ (pow_pos hW _)).mpr (hb i x ξ)
    change ‖∑' i, u i • d i‖ * W^n ≤ H * C * W
    calc
      _ ≤ (H * (C * W / W^n)) * W^n :=
        mul_le_mul_of_nonneg_right (weightedTsum_bound hu hd) (pow_nonneg hW.le _)
      _ = H * C * W := by field_simp
  · intro n
    obtain ⟨C, hC, hb⟩ := ha.pureBaseOrder n
    refine ⟨H * C, mul_nonneg hH hC, fun x ξ => ?_⟩
    rw [(summableSymbolSum_base_jets ha hu ξ).2]
    exact (weightedTsum_bound hu (fun i => hb i x ξ)).trans_eq (by dsimp only [H]; ring)
  · refine continuous_iff_continuousAt.mpr fun p => ?_
    obtain ⟨C, hC, hb⟩ := ha.frequencyOrder 0
    let s := (univ : Set Space) ×ˢ ball p.2 1
    let f (i : ℕ) (q : Space × Space) := u i • a i q.1 q.2
    have hOpen : IsOpen s := isOpen_univ.prod isOpen_ball
    have hp : p ∈ s := ⟨mem_univ _, mem_ball_self zero_lt_one⟩
    have hf (i : ℕ) : Continuous (f i) := (ha.jointlyContinuous i).const_smul _
    have hDom (i : ℕ) (q : Space × Space) (hq : q ∈ s) : ‖f i q‖ ≤ ‖u i‖ * (C * (2 + ‖p.2‖)) := by
      rw [show f i q = u i • a i q.1 q.2 from rfl, norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hVal : ‖a i q.1 q.2‖ ≤ C * (1 + ‖q.2‖) := by
        simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hb i q.1 q.2
      exact hVal.trans (mul_le_mul_of_nonneg_left (one_add_norm_le_of_mem_ball hq.2) hC)
    change ContinuousAt (fun q => ∑' i, f i q) p
    exact (continuousOn_tsum (fun i => (hf i).continuousOn) (hu.mul_right _) hDom).continuousAt
      (hOpen.mem_nhds hp)

end Burnett.Analysis.CarlesonEmbedding
