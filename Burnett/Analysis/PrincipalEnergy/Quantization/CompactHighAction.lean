import Burnett.Analysis.PrincipalEnergy.Quantization.CompactCoordinateBounds

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function Set MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse
open scoped ContDiff

/-- The infrared factor preserves the compact base support and all pure base
symbol estimates with no increase in the constants. -/
theorem compactBaseOrderOne_firstOrderHighSymbol {a : E → E → ℂ} (ha : CompactBaseOrderOne a) :
    CompactBaseOrderOne (firstOrderHighSymbol a) where
  support := by
    obtain ⟨K,hK,hS⟩ := ha.support
    refine ⟨K,hK,fun ξ => ?_⟩
    have hSub : tsupport (fun x => firstOrderHighSymbol a x ξ) ⊆ tsupport (fun x => a x ξ) :=
      closure_mono (support_const_smul_subset ((1-radialCore ξ : ℝ) : ℂ) (fun x => a x ξ))
    exact hSub.trans (hS ξ)
  smooth ξ := (ha.smooth ξ).const_smul ((1-radialCore ξ : ℝ) : ℂ)
  order n := by
    obtain ⟨C,hC,hBound⟩ := ha.order n
    refine ⟨C,hC,?_⟩
    intro x ξ
    let r : ℂ := ((1-radialCore ξ : ℝ) : ℂ)
    have hr : ‖r‖ ≤ 1 := by
      rw [show ‖r‖ = ‖((1-radialCore ξ : ℝ) : ℂ)‖ from rfl,
        Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
      linarith only [radialCore_nonneg ξ]
    have hS : ContDiffAt ℝ n (fun y => a y ξ) x :=
      (ha.smooth ξ).contDiffAt.of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n (r • (fun y => a y ξ)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply hS,norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans (hBound x ξ)

/-- Actual (H^1\to L^2) on the high-frequency branch of a compact-base
first-order scalar quantization, with the same Schwartz inputs. -/
theorem exists_compactBase_firstOrderHighAction_h1_to_l2 {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hs : Continuous (uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap E ℂ,
      ∃ hB : MemLp (firstOrderHighAction a f) 2 (volume : Measure E),
        ‖hB.toLp (firstOrderHighAction a f)‖ ^ 2 ≤ C ^ 2 * schwartzH1Energy f := by
  have hCont : Continuous (uncurry (firstOrderHighSymbol a)) :=
    (Complex.continuous_ofReal.comp
      (continuous_const.sub (radialCore_contDiff.continuous.comp continuous_snd))).mul hs
  exact exists_compactBase_firstOrderAction_h1_to_l2 (compactBaseOrderOne_firstOrderHighSymbol ha) hCont

end Burnett.Analysis.FirstOrderDyadic
