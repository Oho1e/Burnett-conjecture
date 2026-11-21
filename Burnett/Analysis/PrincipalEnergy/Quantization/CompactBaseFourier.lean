import Burnett.Analysis.PrincipalEnergy.Quantization.ActualDerivative
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform

/-- The pure base derivatives of a compactly based symbol are uniformly of
first order before its frequency weight is removed. -/
structure CompactBaseOrderOne (a : E → E → ℂ) : Prop where
  support : ∃ K : Set E, IsCompact K ∧ ∀ ξ, tsupport (fun x => a x ξ) ⊆ K
  smooth : ∀ ξ, ContDiff ℝ ∞ (fun x => a x ξ)
  order : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖)

def normalizedBaseSymbol (a : E → E → ℂ) (x ξ : E) : ℂ :=
  (1 + ‖ξ‖)⁻¹ • a x ξ

def normalizedBaseFourier (a : E → E → ℂ) (k ξ : E) : ℂ :=
  (𝓕 (fun x => normalizedBaseSymbol a x ξ)) k

private theorem normalizedBase_tsupport {a : E → E → ℂ} (ξ : E) :
    tsupport (fun x => normalizedBaseSymbol a x ξ) ⊆ tsupport (fun x => a x ξ) :=
  closure_mono (Function.support_const_smul_subset _ _)

private def normalizedBaseSchwartz {a : E → E → ℂ} (ha : CompactBaseOrderOne a)
    (ξ : E) : SchwartzMap E ℂ :=
  (by
    obtain ⟨K,hK,hSupport⟩ := ha.support
    exact hK.of_isClosed_subset isClosed_closure ((normalizedBase_tsupport ξ).trans (hSupport ξ)) :
    HasCompactSupport (fun x => normalizedBaseSymbol a x ξ)).toSchwartzMap
      ((ha.smooth ξ).const_smul _)

private theorem normalizedBase_deriv_bound {a : E → E → ℂ} (ha : CompactBaseOrderOne a)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖iteratedFDeriv ℝ n (fun y => normalizedBaseSymbol a y ξ) x‖ ≤ C := by
  obtain ⟨C,hC,hBound⟩ := ha.order n
  refine ⟨C,hC,?_⟩
  intro x ξ
  have hw : 0 < 1 + ‖ξ‖ := by positivity
  have hs : ContDiffAt ℝ n (fun y => a y ξ) x :=
    (ha.smooth ξ).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [show (fun y => normalizedBaseSymbol a y ξ) = (1 + ‖ξ‖)⁻¹ • (fun y => a y ξ) from rfl,
    iteratedFDeriv_const_smul_apply hs,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw.le)]
  exact (mul_le_mul_of_nonneg_left (hBound x ξ) (inv_nonneg.mpr hw.le)).trans_eq (by
    field_simp)

theorem normalizedBaseSchwartz_bounded {a : E → E → ℂ} (ha : CompactBaseOrderOne a) :
    Bornology.IsVonNBounded ℂ (Set.range (normalizedBaseSchwartz ha)) := by
  classical
  rw [← image_univ]
  apply ((schwartz_withSeminorms ℂ E ℂ).image_isVonNBounded_iff_seminorm_bounded _).mpr
  rintro ⟨k,n⟩
  obtain ⟨K,hK,hSupport⟩ := ha.support
  obtain ⟨C,hC,hBound⟩ := normalizedBase_deriv_bound ha n
  obtain ⟨R,hR⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let M := (max R 0) ^ k * C
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg (le_max_right _ _) _) hC
  refine ⟨M+1, by positivity, fun ξ _ => ?_⟩
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ k n (normalizedBaseSchwartz ha ξ) hM ?_)
    (lt_add_one _)
  intro x
  by_cases hx : x ∈ K
  · have hn : ‖x‖ ≤ max R 0 := (hR (mem_image_of_mem norm hx)).trans (le_max_left _ _)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn _) (hBound x ξ) (norm_nonneg _)
      (pow_nonneg (le_max_right _ _) _)
  · have hz : iteratedFDeriv ℝ n (normalizedBaseSchwartz ha ξ : E → ℂ) x = 0 := by
      by_contra h
      exact hx (hSupport ξ (normalizedBase_tsupport ξ (support_iteratedFDeriv_subset n h)))
    simpa only [hz, norm_zero, mul_zero] using hM

/-- A single integrable Schwartz-tail envelope controls the actual base
Fourier transform of the normalized symbol at every original frequency. -/
theorem normalizedBaseFourier_dominated {a : E → E → ℂ} (ha : CompactBaseOrderOne a) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun k : E => C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹) ∧
      ∀ k ξ, ‖normalizedBaseFourier a k ξ‖ ≤ C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹ := by
  let U := normalizedBaseSchwartz ha
  let F := SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)
  have hBounded : Bornology.IsVonNBounded ℂ (Set.range fun ξ => F (U ξ)) := by
    change Bornology.IsVonNBounded ℂ (Set.range (F ∘ U))
    rw [Set.range_comp]
    exact (normalizedBaseSchwartz_bounded ha).image F
  rw [← image_univ] at hBounded
  have hBound := ((schwartz_withSeminorms ℂ E ℂ).image_isVonNBounded_iff_seminorm_bounded
    (fun ξ => F (U ξ))).mp hBounded
  obtain ⟨C₀,hC₀,h₀⟩ := hBound (0,0)
  obtain ⟨C₆,hC₆,h₆⟩ := hBound (6,0)
  let C := 8 * (C₀+C₆)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_,?_⟩
  · have hr : (Module.finrank ℝ E : ℝ) < 6 := by norm_num [finrank_euclideanSpace_fin]
    have hInt := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E)) hr).const_mul C
    refine hInt.congr (Eventually.of_forall fun k => ?_)
    change C * (1 + ‖k‖ ^ 2) ^ (-(6 : ℝ)/2) = C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
    rw [show -(6 : ℝ)/2 = -(3 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_natCast]
  · intro k ξ
    let z := ‖normalizedBaseFourier a k ξ‖
    have hz : 0 ≤ z := norm_nonneg _
    have hz₀ : z ≤ C₀ := (SchwartzMap.norm_le_seminorm ℂ (F (U ξ)) k).trans (h₀ ξ (mem_univ _)).le
    have hz₆ : ‖k‖ ^ 6 * z ≤ C₆ :=
      (SchwartzMap.norm_pow_mul_le_seminorm ℂ (F (U ξ)) 6 k).trans (h₆ ξ (mem_univ _)).le
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖k‖ ^ 2) ^ 3)).mpr
    change z * (1 + ‖k‖ ^ 2) ^ 3 ≤ C
    by_cases hk : ‖k‖ ≤ 1
    · have he : (1 + ‖k‖^2)^3 ≤ 8 := by
        have he' := pow_le_pow_left₀ (norm_nonneg k) hk 2
        exact (pow_le_pow_left₀ (by positivity) (add_le_add_left he' 1) 3).trans (by norm_num)
      exact (mul_le_mul hz₀ he (by positivity) hC₀.le).trans (by dsimp [C]; linarith)
    · have he : (1 + ‖k‖^2)^3 ≤ 8 * ‖k‖^6 := by
        have he' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (le_of_not_ge hk) 2
        calc
          _ ≤ (2 * ‖k‖^2)^3 := pow_le_pow_left₀ (by positivity) (by linarith only [he']) 3
          _ = _ := by ring
      calc
        _ ≤ z * (8 * ‖k‖^6) := mul_le_mul_of_nonneg_left he hz
        _ = 8 * (‖k‖^6 * z) := by ring
        _ ≤ _ := by dsimp [C]; linarith

end Burnett.Analysis.FirstOrderDyadic
