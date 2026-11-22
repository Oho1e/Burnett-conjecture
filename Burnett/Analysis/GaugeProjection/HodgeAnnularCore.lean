import Burnett.Analysis.GaugeProjection.HodgePhysicalAction

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.P01

open Set Filter
open Burnett.A02.FrequencySplit
open scoped FourierTransform ContDiff Topology BigOperators

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

/-- The actual Hodge symbol sends a Schwartz vector with compact radian spectrum
away from zero to the exact Schwartz pair used in the commutator identity. -/
theorem exists_hodgeTransverseSchwartz_of_compactSpectrum (w : HodgeSchwartzField)
    (K : Set E) (hK : IsCompact K) (h0 : (0 : E) ∉ K)
    (hw : ∀ j, tsupport (radianFourier (w j : E → ℂ)) ⊆ K) :
    ∃ A : HodgeSchwartzField,
      (∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) ∧
      (∀ i, hodgeTransverseAction w i = (A i : E → ℂ)) := by
  let D : E ≃L[ℝ] E :=
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) tau tau_pos.ne').toContinuousLinearEquiv
  let S (i j : Fin 4) := radianActionSpectrum (directionProjectionEntry i j) (w j)
  have hD (ξ : E) : D ξ = tau • ξ := rfl
  have hzero : (0 : E) ∉ D ⁻¹' K := by
    change D 0 ∉ K
    rw [map_zero]
    exact h0
  have hCompact : IsCompact (D ⁻¹' K) :=
    D.toHomeomorph.isCompact_preimage.mpr hK
  have hS (i j : Fin 4) : tsupport (S i j) ⊆ D ⁻¹' K := by
    apply closure_minimal _ hCompact.isClosed
    intro ξ hξ
    apply hw j
    apply subset_tsupport
    intro hzero
    apply Function.mem_support.mp hξ
    simpa [S, radianActionSpectrum, hD, radianFourier_scaled] using
      congrArg (fun v : ℂ => (directionProjectionEntry i j (tau • ξ) : ℂ) * v) hzero
  have smooth (i j : Fin 4) : ContDiff ℝ ∞ (S i j) := by
    have hoff := radianActionSpectrum_smooth (directionProjectionEntry i j)
      (directionProjectionEntry_contDiffOn i j) (w j)
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      have e : S i j =ᶠ[𝓝 (0 : E)] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hz => hzero (hS i j hz))
      exact contDiffAt_const.congr_of_eventuallyEq e
    · exact hoff.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)
  have hc (i j : Fin 4) : HasCompactSupport (S i j) :=
    hCompact.of_isClosed_subset isClosed_closure (hS i j)
  let B (i j : Fin 4) : SchwartzMap E ℂ := (hc i j).toSchwartzMap (smooth i j)
  let F (i : Fin 4) := ∑ j, B i j
  let A (i : Fin 4) := (SchwartzMap.fourierTransformCLE ℂ).symm (F i)
  have e (ξ : E) (i : Fin 4) : 𝓕 (A i : E → ℂ) ξ = F i ξ :=
    congrArg (fun a : SchwartzMap E ℂ => a ξ)
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (F i))
  have hspectrum (ξ : E) : hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ) := by
    ext i
    have hscale : tau • (tau⁻¹ • ξ) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
    have hF : F i (tau⁻¹ • ξ) = ∑ j, B i j (tau⁻¹ • ξ) := by
      let evaluation : SchwartzMap E ℂ →+ ℂ :=
        { toFun := fun v => v (tau⁻¹ • ξ), map_zero' := rfl, map_add' := fun _ _ => rfl }
      exact map_sum evaluation (B i) Finset.univ
    change radianFourier (A i) ξ = _
    rw [← hscale, radianFourier_scaled, e, hF, hodgeTransverse_apply]
    apply Finset.sum_congr rfl
    intro j _
    change (directionProjectionEntry i j (tau • (tau⁻¹ • ξ)) : ℂ) *
      𝓕 (w j : E → ℂ) (tau⁻¹ • ξ) = _
    exact congrArg (fun z : ℂ => (directionProjectionEntry i j (tau • (tau⁻¹ • ξ)) : ℂ) * z)
      (radianFourier_scaled (w j) (tau⁻¹ • ξ)).symm
  exact ⟨A, hspectrum, fun i => hodgeTransverseAction_eq_of_spectrum w A hspectrum i⟩

end Burnett.P01
