import Burnett.Analysis.PrincipalEnergy.Quantization.NormalizedBaseIdentification
import Burnett.Analysis.PrincipalEnergy.Quantization.SmoothSymbolDerivative

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Function Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff

/-- Taking a base derivative preserves compact base support and the same
first-order frequency weight. The new base seminorm uses one more derivative. -/
theorem compactBaseOrderOne_baseDirection {a : E → E → ℂ} (ha : CompactBaseOrderOne a)
    (e : E) : CompactBaseOrderOne (baseDirectionSymbol a e) where
  support := by
    obtain ⟨K,hK,hS⟩ := ha.support
    refine ⟨K,hK,fun ξ => ?_⟩
    apply (show tsupport (fun x => baseDirectionSymbol a e x ξ) ⊆
      tsupport (fderiv ℝ (fun x => a x ξ)) from ?_).trans
      ((tsupport_fderiv_subset ℝ).trans (hS ξ))
    apply closure_mono
    intro x hx hz
    apply hx
    change fderiv ℝ (fun y => a y ξ) x e = 0
    change fderiv ℝ (fun y => a y ξ) x = 0 at hz
    rw [hz, ContinuousLinearMap.zero_apply]
  smooth ξ :=
    ((ha.smooth ξ).fderiv_right (by simp)).clm_apply contDiff_const
  order n := by
    obtain ⟨C,hC,hBound⟩ := ha.order (n+1)
    refine ⟨‖e‖ * C,mul_nonneg (norm_nonneg _) hC,?_⟩
    intro x ξ
    have hDiff : ContDiff ℝ ∞ (fderiv ℝ (fun y => a y ξ)) :=
      (ha.smooth ξ).fderiv_right (by simp)
    change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (fun z => a z ξ) y e) x‖ ≤ _
    calc
      _ ≤ ‖e‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => a z ξ)) x‖ :=
        norm_iteratedFDeriv_clm_apply_const hDiff.contDiffAt (by exact_mod_cast le_top)
      _ = ‖e‖ * ‖iteratedFDeriv ℝ (n+1) (fun z => a z ξ) x‖ := by
        rw [norm_iteratedFDeriv_fderiv]
      _ ≤ ‖e‖ * (C * (1 + ‖ξ‖)) := mul_le_mul_of_nonneg_left (hBound x ξ) (norm_nonneg _)
      _ = _ := by ring

/-- Joint continuity of the base directional derivative of a jointly smooth
symbol, in the same base and frequency variables. -/
theorem baseDirectionSymbol_joint_continuous {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (e : E) :
    Continuous (uncurry (baseDirectionSymbol a e)) := by
  let L := ContinuousLinearMap.inl ℝ E E
  have hDiff : Differentiable ℝ (uncurry a) := ha.differentiable (by simp)
  have hEq : uncurry (baseDirectionSymbol a e) =
      (fun p => fderiv ℝ (uncurry a) p (e,0)) := by
    funext p
    have hLine : HasFDerivAt (fun y => (y,p.2)) L p.1 := by
      exact (L.hasFDerivAt.add_const (0,p.2)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [L])
    have hA := (hDiff p).hasFDerivAt.comp p.1 hLine
    change fderiv ℝ (uncurry a ∘ fun y => (y,p.2)) p.1 e = _
    rw [hA.fderiv]
    rfl
  rw [hEq]
  exact (ha.continuous_fderiv (by simp)).clm_apply continuous_const

end Burnett.Analysis.FirstOrderDyadic
