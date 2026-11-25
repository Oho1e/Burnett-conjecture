import Burnett.Analysis.AllScaleTransfer.ActualNearCapDecomposition

set_option autoImplicit false
set_option maxHeartbeats 4100000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps

/-- Divide the actual localized coefficient by its source scale before
applying the parabolic change. Measurability, boundedness and the
degree-zero scaling are inherited from the same physical symbol. -/
theorem capLocalizedNearSymbol_core_properties
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (m : Joint → ℂ) (hm : Measurable m) (B : ℝ) (hB : ∀ p, ‖m p‖ ≤ B)
    (hom : ∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p)
    (γ : ↑S.centers) :
    let core := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
    Measurable core ∧ (∀ p, ‖core p‖ ≤ (δ^2)⁻¹ * B) ∧
      ∀ t : ℝ, 0 < t → ∀ p : Joint, core (t • p) = core p := by
  intro core
  let P := capMultiplier S.centers metric δ η inner outer (γ : Vec)
  have hp : Measurable P :=
    measurable_of_continuousOn_compl_singleton (0 : Vec) (S.smoothness γ γ.property).1.continuousOn
  have measMask : Measurable (fun p : Joint => (P p.1 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hp.comp measurable_fst)
  have hs : Measurable (capLocalizedNearSymbol S m γ) := measMask.mul hm
  have hScale : 0 ≤ (δ^2)⁻¹ := inv_nonneg.mpr (sq_nonneg δ)
  have hMeas : Measurable (fun p : Joint => (δ^2)⁻¹ • capLocalizedNearSymbol S m γ p) :=
    measurable_const.smul hs
  refine ⟨hMeas,?_,?_⟩
  · intro p
    have hRange := S.base_range γ γ.property p.1
    change ‖(δ^2)⁻¹ • ((P p.1 : ℂ) * m p)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg hScale,norm_mul,Complex.norm_real,Real.norm_of_nonneg hRange.1]
    exact mul_le_mul_of_nonneg_left
      (((mul_le_mul_of_nonneg_right hRange.2 (norm_nonneg (m p))).trans_eq (one_mul _)).trans (hB p)) hScale
  · intro t ht p
    change (δ^2)⁻¹ • ((P (t • p.1) : ℂ) * m (t • p)) = (δ^2)⁻¹ • ((P p.1 : ℂ) * m p)
    have eq : P (t • p.1) = P p.1 :=
      capMultiplier_degreeZero S.centers metric δ η inner outer γ t ht.ne' p.1
    rw [eq,hom t ht p]

end Burnett.A05
