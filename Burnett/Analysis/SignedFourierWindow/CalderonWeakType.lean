import Burnett.Analysis.SignedFourierWindow.CalderonWeakEstimate
import Burnett.Analysis.SignedFourierWindow.CalderonKernelL2

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- Weak type (1,1) for a bounded continuous physical kernel satisfying an
integral Hörmander condition and an L² bound on Schwartz tests. -/
theorem kernel_weak_type (K : Space → ℂ) (hK : Continuous K) (h2 : MemLp K 2 volume)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (B : ℝ) (hB : 0 ≤ B)
    (test : ∀ f : SchwartzMap Space ℂ, ∃ u : Burnett.Fourier.ComplexL2 Space,
      (u : Space → ℂ) =ᵐ[volume] kernelApply K f ∧ ‖u‖ ≤ B*‖f.toLp 2 volume‖)
    (A : ℝ≥0∞) (hA : ∀ h : Space, (∫⁻ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ A)
    (f : Space → ℂ) (hmf : Measurable f) (hf : Integrable f) (level : ℝ≥0) (hlevel : 0 < level) :
    (level : ℝ≥0∞) * volume {x | (level : ℝ≥0∞) < ‖kernelApply K f x‖ₑ} ≤
      (2*(4096+768*(ENNReal.ofReal B)^2+2*A))*∫⁻ y, ‖f y‖ₑ := by
  classical
  let a : ℝ≥0∞ := ↑(level/2 : ℝ≥0)
  have ha : 0 < a := ENNReal.coe_pos.mpr (div_pos hlevel (by norm_num))
  have haf : a < ⊤ := ENNReal.coe_lt_top
  have half : (level : ℝ≥0∞) = 2*a := by
    change (level : ℝ≥0∞) = 2 * ((level/2 : ℝ≥0) : ℝ≥0∞)
    exact_mod_cast (show level = 2*(level/2) by field_simp)
  obtain ⟨u,r,Q,hu,hd,geom,hmg,rebuild,cap,blocks,mass,exc⟩ := calderon_decomposition f hmf hf a ha
  letI : Countable u := hu.to_subtype
  let V := ⋃ i : u, closedBall (i:Space) (8*r i)
  let g := goodPart f Q
  let b := fun i : u => badBlock f (Q i)
  let M := ∫⁻ y, ‖f y‖ₑ
  have Mfin : M < ⊤ := hf.2
  have hb (i : u) : Measurable (b i) := (hmf.sub measurable_const).indicator (geom i).1
  have hs (i : u) (y : Space) (hy : y ∉ closedBall (i:Space) (4*r i)) : b i y = 0 :=
    indicator_of_notMem (fun h => hy ((geom i).2.2 h)) _
  obtain ⟨hgi,_,hg2,energy⟩ := good_energy f g b hf hmg (fun i => (blocks i).1) rebuild mass a haf cap
  have sumfin := mass.trans_lt (ENNReal.mul_lt_top (by norm_num) Mfin)
  have conv (x : Space) : kernelApply K f x - kernelApply K g x = ∑' i, kernelApply K (b i) x := by
    rw [kernel_split_apply K hK D hD f g hf hgi b (fun i => (blocks i).1) sumfin rebuild,add_sub_cancel_left]
  have off : (∫⁻ x in Vᶜ, ‖kernelApply K f x - kernelApply K g x‖ₑ) ≤ A*(2*M) := by
    simp_rw [conv]
    exact (bad_sum_exterior K hK D hD A hA b hb (fun i => (blocks i).1) (fun i => (blocks i).2)
      (fun i : u => (i:Space)) (fun i => r i) hs).trans (mul_le_mul_left' mass _)
  have output := good_output_energy g (kernelApply K g) a M (ENNReal.ofReal B)
    (kernelApply_L2_extension K h2 B hB test g hg2) energy
  have weak := weak_from_good_bad (kernelApply K f) (kernelApply K g) (measurable_kernelApply _ _ hK hmf)
    (measurable_kernelApply _ _ hK hmg) V a M (ENNReal.ofReal B) A ha haf exc output off
  rw [half]
  simpa only [mul_assoc] using mul_le_mul_left' weak 2

end Burnett.Analysis.SignedFourierWindow
