import Burnett.Analysis.SignedFourierWindow.InterpolationTruncate

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set
open scoped ENNReal

/-- The distribution estimate at one height. Integration in the height variable
will use the upper L¹ and lower L² terms with different powers. -/
theorem interpolation_level (K : Space → ℂ) (hK : Continuous K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    (W B : ℝ≥0∞)
    (weak : ∀ h : Space → ℂ, Integrable h → ∀ t : ℝ, 0<t →
      ENNReal.ofReal t * volume {x | t < ‖kernelApply K h x‖} ≤ W * ∫⁻ x, ‖h x‖ₑ)
    (strong : ∀ l : Space → ℂ, MemLp l 2 volume → eLpNorm (kernelApply K l) 2 volume ≤ B*eLpNorm l 2 volume)
    (f : Space → ℂ) (hm : Measurable f) (hf : Integrable f) (t p : ℝ) (ht : 0<t) :
    volume {x | t < ‖kernelApply K f x‖/2} * ENNReal.ofReal (t^(p-1)) ≤
      W*((∫⁻ x, upperTail (fun y => ENNReal.ofReal ‖f y‖) (ENNReal.ofReal t) x) * ENNReal.ofReal (t^(p-1-1))) +
      B^2*((∫⁻ x in {x : Space | ‖f x‖ ≤ t}, (ENNReal.ofReal ‖f x‖)^2) * ENNReal.ofReal (t^(p-3))) := by
  obtain ⟨h,l,hi,lm,l2,split,high,low⟩ := kernel_height_split K hK D hD f hm hf t ht
  let H := {x : Space | t < ‖kernelApply K h x‖}
  let L := {x : Space | ENNReal.ofReal t ≤ ‖kernelApply K l x‖ₑ}
  have cover : {x : Space | t < ‖kernelApply K f x‖/2} ⊆ H ∪ L := by
    intro x hx
    by_cases hH : x ∈ H
    · exact Or.inl hH
    right
    have hx' : t < ‖kernelApply K f x‖/2 := hx
    have hh : ‖kernelApply K h x‖ ≤ t := not_lt.mp hH
    rw [split] at hx'
    have : t ≤ ‖kernelApply K l x‖ := by linarith [norm_add_le (kernelApply K h x) (kernelApply K l x)]
    exact (ENNReal.ofReal_le_ofReal this).trans_eq (ofReal_norm_eq_enorm _)
  have hh := weak h hi t ht
  rw [high] at hh
  have ll : (ENNReal.ofReal t)^2 * volume L ≤ B^2*∫⁻ x in {x : Space | ‖f x‖ ≤ t}, (ENNReal.ofReal ‖f x‖)^2 := by
    have cheb := mul_meas_ge_le_pow_eLpNorm' (volume : Measure Space) (p := 2) (by norm_num) (by norm_num)
      (measurable_kernelApply K l hK lm).aestronglyMeasurable (ENNReal.ofReal t)
    simp only [ENNReal.toReal_ofNat,ENNReal.rpow_two] at cheb
    exact cheb.trans ((pow_le_pow_left' (strong l l2) 2).trans_eq (by rw [mul_pow,low]))
  have p₁ : ENNReal.ofReal (t^(p-1)) = ENNReal.ofReal t * ENNReal.ofReal (t^(p-1-1)) := by
    rw [← ENNReal.ofReal_mul ht.le]
    congr 1
    rw [show p-1=(p-1-1)+1 by ring,Real.rpow_add_one ht.ne']
    ring_nf
  have p₂ : ENNReal.ofReal (t^(p-1)) = (ENNReal.ofReal t)^2 * ENNReal.ofReal (t^(p-3)) := by
    rw [← ENNReal.ofReal_pow ht.le,← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [← Real.rpow_two,← Real.rpow_add ht]
    ring_nf
  calc
    _ ≤ (volume H+volume L)*ENNReal.ofReal (t^(p-1)) :=
      mul_le_mul_right' ((measure_mono cover).trans (measure_union_le _ _)) _
    _ = ((ENNReal.ofReal t)*volume H)*ENNReal.ofReal (t^(p-1-1)) +
        ((ENNReal.ofReal t)^2*volume L)*ENNReal.ofReal (t^(p-3)) := by
      rw [add_mul]; congr 1
      · rw [p₁]; ac_rfl
      · rw [p₂]; ac_rfl
    _ ≤ _ := by
      simpa only [mul_assoc] using add_le_add (mul_le_mul_right' hh (ENNReal.ofReal (t^(p-1-1))))
        (mul_le_mul_right' ll (ENNReal.ofReal (t^(p-3))))

end Burnett.Analysis.SignedFourierWindow
