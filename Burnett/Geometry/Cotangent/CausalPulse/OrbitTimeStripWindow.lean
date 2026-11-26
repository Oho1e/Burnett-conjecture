import Burnett.Geometry.Cotangent.CausalPulse.CausalOrbitPulse

set_option autoImplicit false
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set MeasureTheory

variable {X : Type*}

/-- Monotonicity and the two endpoint values exhaust the support of a pulse
on a time strip, regardless of the affine orientation. -/
theorem timeStripPulse_zero_outside_window (T f : X → ℝ) (γ : ℝ → X) {I : Set ℝ} {a b l u : ℝ}
    (hl : l < u) (hSupport : Function.support f = T ⁻¹' Ioo l u)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b)
    (hMonotone : MonotoneOn (T ∘ γ) I ∨ AntitoneOn (T ∘ γ) I)
    (hEnds : (T (γ a) < l ∧ u < T (γ b)) ∨ (u < T (γ a) ∧ T (γ b) < l)) :
    ∀ t ∈ I, t ∉ Icc a b → f (γ t) = 0 := by
  intro t ht htOut
  have hToZero (hn : T (γ t) ∉ Ioo l u) : f (γ t) = 0 := by
    by_contra h
    apply hn
    change γ t ∈ T ⁻¹' Ioo l u
    rw [← hSupport]
    exact h
  have hOut : t < a ∨ b < t := by
    by_cases h : t < a
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge fun h' => htOut ⟨le_of_not_gt h, h'⟩)
  apply hToZero
  intro hMem
  rcases hMonotone with hMon | hAnti
  · rcases hEnds with h | h
    · rcases hOut with hlt | hgt
      · exact (not_lt_of_ge ((hMon ht ha hlt.le).trans h.1.le)) hMem.1
      · exact (not_lt_of_ge (h.2.le.trans (hMon hb ht hgt.le))) hMem.2
    · exact (not_lt_of_ge (h.2.le.trans hl.le)) (h.1.trans_le (hMon ha hb hab))
  · rcases hEnds with h | h
    · exact (not_lt_of_ge (h.1.le.trans hl.le)) (h.2.trans_le (hAnti ha hb hab))
    · rcases hOut with hlt | hgt
      · exact (not_lt_of_ge (h.1.le.trans (hAnti ht ha hlt.le))) hMem.2
      · exact (not_lt_of_ge ((hAnti hb ht hgt.le).trans h.2.le)) hMem.1

theorem pulseIntegral_eq_integral_window (f : X → ℝ) (γ : ℝ → X) {I : Set ℝ} {a b : ℝ}
    (hSub : Icc a b ⊆ I) (hOutside : ∀ t ∈ I, t ∉ Icc a b → f (γ t) = 0) :
    pulseIntegral f γ I = ∫ t in Icc a b, f (γ t) := by
  have hEq : I.indicator (f ∘ γ) = (Icc a b).indicator (f ∘ γ) := by
    funext t
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht, indicator_of_mem (hSub ht)]
    · rw [indicator_of_notMem ht]
      by_cases hI : t ∈ I
      · rw [indicator_of_mem hI]
        exact hOutside t hI ht
      · exact indicator_of_notMem hI _
  rw [pulseIntegral, hEq, integral_indicator measurableSet_Icc]
  rfl

end Burnett.Geometry.CausalOrbitPulse
