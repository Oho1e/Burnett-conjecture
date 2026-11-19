import Burnett.Analysis.SignedFourierWindow.SquareProduct
import Burnett.Analysis.SignedFourierWindow.FiniteLowWindow

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Finset MeasureTheory
open scoped NNReal ENNReal

private theorem three_point {n : ℕ} (u v : Fin n → ℂ) (w : Fin n → Space → ℂ) (x : Space) :
    (∑ i, ‖u i‖*‖v i‖*‖w i x‖) ≤ Real.sqrt (vectorEnergy u)*Real.sqrt (vectorEnergy v)*finiteAmplitude w x := by
  have hb (i : Fin n) : ‖w i x‖ ≤ finiteAmplitude w x := by
    exact_mod_cast (le_sup (f := fun i => ‖w i x‖₊) (mem_univ i))
  have hn : 0 ≤ finiteAmplitude w x := NNReal.coe_nonneg _
  calc
    _ ≤ ∑ i, ‖u i‖*‖v i‖*finiteAmplitude w x := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hb i) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (∑ i, ‖u i‖*‖v i‖)*finiteAmplitude w x := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hn

/-- Summed absolute trilinear spatial products with two annular factors and one
low-pass factor. All three dilations may be chosen independently, with distinct
dyadic scales in each annular family and arbitrary positive scales in the third. -/
theorem two_annular_one_low (a b d : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (hb : HasCompactSupport (b : Space → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z)
    (m : ℝ≥0∞) [ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal s) m]
    [ENNReal.HolderTriple m (ENNReal.ofReal z) 1] :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (t u : ℝ), 0<t → 0<u → ∀ (q v l : Space) (n : ℕ) (e j : Fin n ↪ ℕ)
      (sc : Fin n → ℝ), (∀ i, 0<sc i) → ∀ (f g : Space → ℂ) (h : SchwartzMap Space ℂ),
      MemLp f (ENNReal.ofReal p) volume → MemLp g (ENNReal.ofReal s) volume →
      (∫⁻ x, ENNReal.ofReal (∑ i, ‖kernelApply (annularKernel a t q (e i)) f x‖*
        ‖kernelApply (annularKernel b u v (j i)) g x‖*‖shiftedWindowOperator d h (sc i) l x‖)) ≤
      (C*ENNReal.ofReal (1+‖q‖)*ENNReal.ofReal (1+‖v‖)*ENNReal.ofReal ((1+‖l‖)^5))*
        eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal s) volume *
        eLpNorm (h : Space → ℂ) (ENNReal.ofReal z) volume := by
  obtain ⟨A,af,aa⟩ := annular_square_all_Lp a ha ca p hp
  obtain ⟨B,bf,bb⟩ := annular_square_all_Lp b hb cb s hs
  obtain ⟨D,df,dd⟩ := finite_low_window_Lp d z hz
  refine ⟨A*B*D,ENNReal.mul_lt_top (ENNReal.mul_lt_top af bf) df,?_⟩
  intro t u ht hu q v l n e j sc hsc f g h hf hg
  let F := annularSquare e a t q f
  let G := annularSquare j b u v g
  let w := fun i : Fin n => shiftedWindowOperator d h (sc i) l
  let H := finiteAmplitude w
  have mf := measurable_annularSquare e a t q f hf.1
  have mg := measurable_annularSquare j b u v g hg.1
  have mh : Measurable H := measurable_finiteAmplitude w (fun i => (shiftedWindow_continuous _ _ _ (hsc i) _).measurable)
  have nn (x : Space) : 0 ≤ (F x*G x)*H x :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (NNReal.coe_nonneg _)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((F x*G x)*H x) := lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (three_point (fun i => kernelApply (annularKernel a t q (e i)) f x)
        (fun i => kernelApply (annularKernel b u v (j i)) g x) w x)
    _ = eLpNorm ((F*G) • H) 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      apply lintegral_congr
      intro x
      exact (Real.enorm_eq_ofReal (nn x)).symm
    _ ≤ eLpNorm (F*G) m volume * eLpNorm H (ENNReal.ofReal z) volume :=
      eLpNorm_smul_le_mul_eLpNorm mh.aestronglyMeasurable (mf.mul mg).aestronglyMeasurable
    _ ≤ (eLpNorm F (ENNReal.ofReal p) volume * eLpNorm G (ENNReal.ofReal s) volume) * eLpNorm H (ENNReal.ofReal z) volume :=
      mul_le_mul_right' (eLpNorm_smul_le_mul_eLpNorm mg.aestronglyMeasurable mf.aestronglyMeasurable) _
    _ ≤ _ := (mul_le_mul' (mul_le_mul' (aa t ht q n e f hf) (bb u hu v n j g hg)) (dd h l n sc hsc)).trans_eq (by ac_rfl)

end Burnett.Analysis.SignedFourierWindow
