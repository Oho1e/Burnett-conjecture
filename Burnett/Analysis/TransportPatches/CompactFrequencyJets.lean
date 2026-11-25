import Burnett.Analysis.TransportPatches.ActualWideInfraredMultipliers
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

/-! Bounds on the actual frequency derivatives of a compact family of symbols. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.C02

open Set Metric
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators ContDiff

local notation "Punctured" => ({0}ᶜ : Set E)

private theorem iteratedFrequencySlice_le_joint (f : E × E → ℝ) {U : Set (E × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (x ξ : E) (hx : (x, ξ) ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun η => f (x, η)) ξ‖ ≤ ‖iteratedFDeriv ℝ n f (x, ξ)‖ := by
  let L := ContinuousLinearMap.inr ℝ E E
  let a : E × E := (x, 0)
  let shift (p : E × E) := a + p
  let V := shift ⁻¹' U
  have hShift : ContDiff ℝ ∞ shift := contDiff_const.add contDiff_id
  have hV : IsOpen V := hU.preimage hShift.continuous
  have hF : ContDiffOn ℝ ∞ (f ∘ shift) V := hf.comp hShift.contDiffOn (mapsTo_preimage _ _)
  have hxV : L ξ ∈ V := by
    change a + L ξ ∈ U
    simpa [a, L] using hx
  have hInv : ξ ∈ L ⁻¹' V := hxV
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hEq := L.iteratedFDerivWithin_comp_right hF hV.uniqueDiffOn
    (hV.preimage L.continuous).uniqueDiffOn hxV hn
  rw [iteratedFDerivWithin_of_isOpen n (hV.preimage L.continuous) hInv,
    iteratedFDerivWithin_of_isOpen n hV hxV] at hEq
  have hShiftDeriv : iteratedFDeriv ℝ n (f ∘ shift) (L ξ) = iteratedFDeriv ℝ n f (x, ξ) := by
    simpa [shift, Function.comp_def, a, L] using (iteratedFDeriv_comp_add_left (f := f) n a (L ξ))
  have hFn : ((f ∘ shift) ∘ L : E → ℝ) = fun η => f (x, η) := by
    funext η
    simp [Function.comp_def, a, L, shift]
  rw [hShiftDeriv, hFn] at hEq
  rw [hEq]
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => by simp [L, Prod.norm_def])
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans (by
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL))

/-- Compactness bounds the actual partial frequency derivatives, using the
joint chart derivative and restriction to the affine frequency fiber. -/
theorem compactChartFamily_uniform_frequency_jets (K U : Set E)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (f : E × E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Punctured)) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ x ∈ K, ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (fun η => f (x, η)) ξ‖ ≤ J := by
  let Ω := U ×ˢ Punctured
  have hΩ : IsOpen Ω := hU.prod isOpen_compl_singleton
  let F := K ×ˢ sphere (0 : E) 1
  have hF : IsCompact F := hK.prod (isCompact_sphere _ _)
  have hFΩ : F ⊆ Ω := by
    intro p hp
    refine ⟨hKU hp.1, ?_⟩
    change p.2 ≠ 0
    intro h0
    have h := hp.2
    change p.2 ∈ sphere (0 : E) 1 at h
    simp [h0] at h
  have hEach (n : ℕ) : ∃ J : ℝ, 0 ≤ J ∧ ∀ p ∈ F, ‖iteratedFDeriv ℝ n f p‖ ≤ J := by
    have hD : ContinuousOn (iteratedFDerivWithin ℝ n f Ω) Ω :=
      hf.continuousOn_iteratedFDerivWithin (mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) hΩ.uniqueDiffOn
    obtain ⟨J, hJ, hBound⟩ := (hF.image_of_continuousOn (hD.mono hFΩ)).isBounded.exists_pos_norm_le
    refine ⟨J, hJ.le, fun p hp => ?_⟩
    have hh := hBound _ (mem_image_of_mem _ hp)
    rwa [iteratedFDerivWithin_of_isOpen n hΩ (hFΩ hp)] at hh
  choose J hJ hBound using hEach
  let C := ∑ n ∈ Finset.range 7, J n
  refine ⟨C, Finset.sum_nonneg (fun n _ => hJ n), ?_⟩
  intro x hx n hn ξ hξ
  have hp : (x, ξ) ∈ F := ⟨hx, hξ⟩
  exact (iteratedFrequencySlice_le_joint f hΩ hf x ξ (hFΩ hp) n).trans
    ((hBound n _ hp).trans
      (Finset.single_le_sum (fun k _ => hJ k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))))

end Burnett.C02
