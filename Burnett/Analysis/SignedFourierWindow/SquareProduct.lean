import Burnett.Analysis.SignedFourierWindow.AnnularSquareLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Finset
open scoped ENNReal

/-- Cauchy–Schwarz in the scale index, with any complex coefficients in the
unit disk. -/
theorem band_product_point {n : ℕ} (u v c : Fin n → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, c i*u i*v i‖ ≤ Real.sqrt (vectorEnergy u) * Real.sqrt (vectorEnergy v) := by
  calc
    _ ≤ ∑ i, ‖c i*u i*v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖u i‖*‖v i‖ := sum_le_sum fun i _ => by
      rw [norm_mul,norm_mul]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (hc i)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem measurable_annularSquare {n : ℕ} (e : Fin n ↪ ℕ) (a : SchwartzMap Space ℂ)
    (t : ℝ) (q : Space) (f : Space → ℂ) (hf : AEStronglyMeasurable f volume) :
    Measurable (annularSquare e a t q f) := by
  have meas (i : Fin n) : Measurable (kernelApply (annularKernel a t q (e i)) f) := by
    refine kernelApply_measurable_ae _ ?_ _ hf
    unfold annularKernel shiftedSpatialKernel
    fun_prop
  exact Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ (fun i _ => (meas i).norm.pow_const 2))

/-- The true finite high–high interaction is uniformly Lᵖ×Lˢ→Lʳ for all
admissible finite exponents, with arbitrary relative choices of distinct scales. -/
theorem annular_product_Lp (a b : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (hb : HasCompactSupport (b : Space → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p s r : ℝ) (hp : 1<p) (hs : 1<s)
    [ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal s) (ENNReal.ofReal r)] :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (t d : ℝ), 0<t → 0<d → ∀ (q v : Space) (n : ℕ) (e j : Fin n ↪ ℕ)
      (c : Fin n → ℂ), (∀ i, ‖c i‖ ≤ 1) → ∀ (f g : Space → ℂ), MemLp f (ENNReal.ofReal p) volume →
      MemLp g (ENNReal.ofReal s) volume →
      eLpNorm (fun x => ∑ i, c i*kernelApply (annularKernel a t q (e i)) f x *
        kernelApply (annularKernel b d v (j i)) g x) (ENNReal.ofReal r) volume ≤
        (C * ENNReal.ofReal (1+‖q‖) * ENNReal.ofReal (1+‖v‖)) *
          eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal s) volume := by
  obtain ⟨U,hU,estU⟩ := annular_square_all_Lp a ha ca p hp
  obtain ⟨V,hV,estV⟩ := annular_square_all_Lp b hb cb s hs
  refine ⟨U*V,ENNReal.mul_lt_top hU hV,?_⟩
  intro t d ht hd q v n e j c hc f g hf hg
  let F := annularSquare e a t q f
  let G := annularSquare j b d v g
  have mF := measurable_annularSquare e a t q f hf.1
  have mG := measurable_annularSquare j b d v g hg.1
  have bound (x : Space) := band_product_point (fun i => kernelApply (annularKernel a t q (e i)) f x)
    (fun i => kernelApply (annularKernel b d v (j i)) g x) c hc
  calc
    _ ≤ eLpNorm (F • G) (ENNReal.ofReal r) volume := by
      apply eLpNorm_mono
      intro x
      change _ ≤ ‖F x * G x‖
      rw [Real.norm_of_nonneg (show 0≤F x*G x from mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      exact bound x
    _ ≤ eLpNorm F (ENNReal.ofReal p) volume * eLpNorm G (ENNReal.ofReal s) volume :=
      eLpNorm_smul_le_mul_eLpNorm mG.aestronglyMeasurable mF.aestronglyMeasurable
    _ ≤ _ := (mul_le_mul' (estU t ht q n e f hf) (estV d hd v n j g hg)).trans_eq (by ac_rfl)

end Burnett.Analysis.SignedFourierWindow
