import Burnett.Analysis.CubicEnergy.HighSymbols
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Set Metric
open scoped ContDiff Topology

/-- All derivatives of a smooth degree-zero symbol are controlled by its derivatives
on the single compact unit sphere of the joint frequency space. -/
theorem degreeZero_derivative_bounds {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [ProperSpace X] (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f {x | x ≠ 0})
    (hhom : ∀ (s : ℝ), 0 < s → ∀ x, f (s • x) = f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, x ≠ 0 → ‖iteratedFDeriv ℝ n f x‖ * ‖x‖^n ≤ C := by
  let U : Set X := {x | x ≠ 0}
  have ho : IsOpen U := isClosed_singleton.isOpen_compl
  have hd : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcont : ContinuousOn (iteratedFDeriv ℝ n f) U :=
    (hf.continuousOn_iteratedFDerivWithin hd ho.uniqueDiffOn).congr (iteratedFDerivWithin_of_isOpen n ho).symm
  have hsU : sphere (0:X) 1 ⊆ U := by
    intro x hx
    have he : ‖x‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hx
    exact norm_ne_zero_iff.mp (he.trans_ne one_ne_zero)
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:X) 1).bddAbove_image (hcont.norm.mono hsU)
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  let s := ‖x‖⁻¹
  have hs : 0 < s := inv_pos.mpr (norm_pos_iff.mpr hx)
  let T : X →L[ℝ] X := s • ContinuousLinearMap.id ℝ X
  have hT (z : X) : T z = s • z := rfl
  have hTU : T x ∈ U := smul_ne_zero hs.ne' hx
  have hpre : IsOpen (T ⁻¹' U) := ho.preimage T.continuous
  have hcomp : f ∘ T = f := funext (hhom _ hs)
  have hder := T.iteratedFDerivWithin_comp_right hf ho.uniqueDiffOn hpre.uniqueDiffOn (x := x) hTU hd
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ T ⁻¹' U from hTU),
      iteratedFDerivWithin_of_isOpen n ho hTU,hcomp] at hder
  have hTle : ‖T‖ ≤ s := T.opNorm_le_bound hs.le (fun z => by rw [hT,norm_smul,Real.norm_of_nonneg hs.le])
  have hsphere : T x ∈ sphere (0:X) 1 := by
    simpa only [mem_sphere,dist_zero_right,hT,s] using (norm_smul_inv_norm (𝕜 := ℝ) hx)
  have hunit : ‖iteratedFDeriv ℝ n f (T x)‖ ≤ C := hC (mem_image_of_mem _ hsphere)
  have hb : ‖iteratedFDeriv ℝ n f x‖ ≤ C * s^n := calc
    _ ≤ ‖iteratedFDeriv ℝ n f (T x)‖ * ‖T‖^n := by
      rw [hder]
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        ((iteratedFDeriv ℝ n f (T x)).norm_compContinuousLinearMap_le (fun _ => T))
    _ ≤ C * s^n := mul_le_mul hunit (pow_le_pow_left₀ (norm_nonneg _) hTle _) (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hunit)
  calc
    _ ≤ (C * s^n) * ‖x‖^n := mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)
    _ = C := by simp only [s,inv_pow,mul_assoc,inv_mul_cancel₀ (pow_ne_zero n (norm_ne_zero_iff.mpr hx)),mul_one]
    _ ≤ _ := le_max_left _ _

theorem joint_derivative_bounds (f : E × E → ℝ) (hf : ContDiffOn ℝ ∞ f {x | x ≠ 0})
    (hhom : ∀ (s : ℝ), 0<s → ∀ x, f (s • x)=f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ξ : E, (η,ξ) ≠ 0 →
      ‖iteratedFDeriv ℝ n f (η,ξ)‖ * (‖η‖+‖ξ‖)^n ≤ C := by
  obtain ⟨K,hK,hbound⟩ := degreeZero_derivative_bounds f hf hhom n
  refine ⟨K*2^n,by positivity,?_⟩
  intro η ξ hp
  have hsize : ‖η‖+‖ξ‖ ≤ ‖(η,ξ)‖*2 := by
    rw [Prod.norm_def]
    linarith [le_max_left ‖η‖ ‖ξ‖,le_max_right ‖η‖ ‖ξ‖]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (η,ξ)‖ * (‖(η,ξ)‖*2)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize _) (norm_nonneg _)
    _ = (‖iteratedFDeriv ℝ n f (η,ξ)‖ * ‖(η,ξ)‖^n) * 2^n := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound _ hp) (by positivity)

end Burnett.A02.FrequencySplit
