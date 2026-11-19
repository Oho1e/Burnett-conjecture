import Burnett.Analysis.SignedFourierWindow.CalderonCancellation

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Finset
open scoped ENNReal

/-- Fixed finite kernels are continuous bounded L¹∩L² functions. The envelope
here may depend on the finite family; it will disappear from the weak-type constant. -/
theorem finite_kernel_regular (φ : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t) (q : Space)
    (I : Finset ℕ) (c : ℕ → ℂ) :
    let K := finiteWindowKernel φ t q I c
    Continuous K ∧ Integrable K ∧ MemLp K 2 volume ∧ ∃ D : ℝ, ∀ z, ‖K z‖ ≤ D := by
  let s := fun k : ℕ => (2:ℝ)^k*t
  have hs (k : ℕ) : 0<s k := mul_pos (by positivity) ht
  let D := ∑ k ∈ I, ‖c k‖ * (|(s k ^ 4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ)
  let K := finiteWindowKernel φ t q I c
  have hcont : Continuous K := by
    change Continuous (fun z : Space => ∑ k ∈ I, c k * shiftedSpatialKernel φ (s k) q z)
    unfold shiftedSpatialKernel
    fun_prop
  have hI : Integrable K := integrable_finset_sum _ (fun k _ =>
    (shiftedSpatialKernel_integrable φ (hs k) q).const_mul (c k))
  have bound (z : Space) : ‖K z‖ ≤ D := by
    refine (norm_sum_le I _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [shiftedSpatialKernel,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (abs_nonneg _)
  have h2 : MemLp K 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
    apply (hI.norm.const_mul D).mono' (hcont.norm.pow 2).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (bound z) (norm_nonneg _)
  exact ⟨hcont,hI,h2,D,bound⟩

end Burnett.Analysis.SignedFourierWindow
