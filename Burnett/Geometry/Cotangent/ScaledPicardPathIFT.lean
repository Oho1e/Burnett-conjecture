import Burnett.Geometry.Cotangent.ContinuousPathIntegral
import Burnett.Geometry.Cotangent.PathSuperposition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped ContDiff Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]

private def scaledResidual {ρ : ℝ} (hρ : 0 ≤ ρ) (f : E → E) (hf : Continuous f)
    (z : ℝ × TimePath ρ E) : ℝ × TimePath ρ E :=
  (z.1, z.2 - z.1 • pathPrimitive hρ (pathSuperposition f hf z.2))

/-- The short-time parameter can be put into the vector field on one fixed
interval. Near zero, the path dependence is jointly smooth in the initial
point and the time scaling parameter. -/
theorem exists_jointSmooth_scaledPicardPaths {ρ : ℝ} (hρ : 0 ≤ ρ) (f : E → E)
    (hf : ContDiff ℝ ∞ f) (x₀ : E) :
    ∃ Φ : E × ℝ → TimePath ρ E, Φ (x₀, 0) = ContinuousMap.const _ x₀ ∧
      ContDiffAt ℝ ∞ Φ (x₀, 0) ∧
      ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), ContDiffAt ℝ ∞ Φ p ∧ ∀ t : Icc (-ρ) ρ,
        Φ p t = p.1 + p.2 • ∫ s in (0 : ℝ)..(t : ℝ), f (Φ p (projIcc (-ρ) ρ (by linarith) s)) := by
  let C : E →L[ℝ] TimePath ρ E := ContinuousLinearMap.const ℝ _
  let z₀ : ℝ × TimePath ρ E := (0, C x₀)
  let H (z : ℝ × TimePath ρ E) : TimePath ρ E :=
    pathPrimitive hρ (pathSuperposition f hf.continuous z.2)
  let G := scaledResidual hρ f hf.continuous
  have hH : ContDiff ℝ ∞ H := (pathPrimitive hρ).contDiff.comp
    ((contDiff_pathSuperposition f hf).comp contDiff_snd)
  have hG : ContDiff ℝ ∞ G :=
    contDiff_fst.prodMk (contDiff_snd.sub (contDiff_fst.smul hH))
  have hz₀ : G z₀ = z₀ := by simp [G, scaledResidual, z₀]
  let fstL := ContinuousLinearMap.fst ℝ ℝ (TimePath ρ E)
  let sndL := ContinuousLinearMap.snd ℝ ℝ (TimePath ρ E)
  let L := fstL.prod (sndL - fstL.smulRight (H z₀))
  have hinj : Function.Injective L := by
    intro z w he
    have hpair : (z.1, z.2 - z.1 • H z₀) = (w.1, w.2 - w.1 • H z₀) := he
    obtain ⟨hfirst, hsecond⟩ := Prod.mk.inj hpair
    rw [hfirst] at hsecond
    exact Prod.ext hfirst (by simpa using congrArg (fun u => u + w.1 • H z₀) hsecond)
  have hsurj : Function.Surjective L := by
    intro w
    refine ⟨(w.1, w.2 + w.1 • H z₀), Prod.ext rfl ?_⟩
    exact add_sub_cancel_right _ _
  let D := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hD : (D : (ℝ × TimePath ρ E) →L[ℝ] (ℝ × TimePath ρ E)) = L :=
    ContinuousLinearEquiv.coe_ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  have hG' : HasFDerivAt G (D : (ℝ × TimePath ρ E) →L[ℝ] (ℝ × TimePath ρ E)) z₀ := by
    rw [hD]
    have hHd : HasFDerivAt H (fderiv ℝ H z₀) z₀ :=
      (hH.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have hprod : HasFDerivAt (fun z : ℝ × TimePath ρ E => z.1 • H z)
        (fstL.smulRight (H z₀)) z₀ := by
      have hz : fstL z₀ = 0 := rfl
      simpa only [hz, zero_smul, zero_add] using
        fstL.hasFDerivAt.fun_smul hHd
    exact fstL.hasFDerivAt.prodMk (sndL.hasFDerivAt.sub hprod)
  let e := hG.contDiffAt.toOpenPartialHomeomorph G hG' (by simp)
  have hsource : z₀ ∈ e.source := hG.contDiffAt.mem_toOpenPartialHomeomorph_source hG' (by simp)
  have htarget : z₀ ∈ e.target := by
    rw [← hz₀]
    exact hG.contDiffAt.image_mem_toOpenPartialHomeomorph_target hG' (by simp)
  have hInverse : ContDiffAt ℝ ∞ (fun w => e.symm w) z₀ := by
    rw [← hz₀]
    exact hG.contDiffAt.to_localInverse hG' (by simp)
  have hInverse₀ : e.symm z₀ = z₀ := by
    have hh := e.left_inv hsource
    change e.symm (G z₀) = z₀ at hh
    rwa [hz₀] at hh
  have hInverseNear : ∀ᶠ w in 𝓝 z₀, ContDiffAt ℝ ∞ (fun a => e.symm a) w := by
    have hInvDeriv : ∀ᶠ z in 𝓝 z₀,
        fderiv ℝ G z ∈ range ((↑) : ((ℝ × TimePath ρ E) ≃L[ℝ] (ℝ × TimePath ρ E)) →
          (ℝ × TimePath ρ E) →L[ℝ] (ℝ × TimePath ρ E)) := by
      apply (hG.continuous_fderiv (by simp)).continuousAt.preimage_mem_nhds
      rw [hG'.fderiv]
      exact D.nhds
    have ht : Tendsto (fun w => e.symm w) (𝓝 z₀) (𝓝 z₀) := by
      simpa only [hInverse₀] using hInverse.continuousAt.tendsto
    filter_upwards [e.open_target.mem_nhds htarget, ht.eventually hInvDeriv] with w hw hderiv
    obtain ⟨A, hA⟩ := hderiv
    apply e.contDiffAt_symm hw
    · rw [hA]
      exact (hG.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    · exact hG.contDiffAt
  let Z (p : E × ℝ) : ℝ × TimePath ρ E := (p.2, C p.1)
  have hZ : ContDiff ℝ ∞ Z := contDiff_snd.prodMk (C.contDiff.comp contDiff_fst)
  let Φ (p : E × ℝ) : TimePath ρ E := (e.symm (Z p)).2
  have hΦ₀ : Φ (x₀, 0) = ContinuousMap.const _ x₀ := congrArg Prod.snd hInverse₀
  have hΦ : ContDiffAt ℝ ∞ Φ (x₀, 0) :=
    contDiff_snd.contDiffAt.comp (x₀, 0) (hInverse.comp (x₀, 0) hZ.contDiffAt)
  have hNear : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), Z p ∈ e.target :=
    hZ.continuous.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds htarget)
  have hZt : Tendsto Z (𝓝 (x₀, (0 : ℝ))) (𝓝 z₀) := hZ.continuous.continuousAt
  refine ⟨Φ, hΦ₀, hΦ, ?_⟩
  filter_upwards [hNear, hZt.eventually hInverseNear] with p hp hsmooth
  refine ⟨contDiff_snd.contDiffAt.comp p (hsmooth.comp p hZ.contDiffAt), ?_⟩
  intro t
  have h := e.right_inv hp
  change G (e.symm (Z p)) = Z p at h
  have hScale : (e.symm (Z p)).1 = p.2 := congrArg Prod.fst h
  have hPath : Φ p - p.2 • pathPrimitive hρ (pathSuperposition f hf.continuous (Φ p)) = C p.1 := by
    have hp' := congrArg Prod.snd h
    change Φ p - (e.symm (Z p)).1 • pathPrimitive hρ
      (pathSuperposition f hf.continuous (Φ p)) = C p.1 at hp'
    rwa [hScale] at hp'
  have pointwise := congrArg (fun u : TimePath ρ E => u t) hPath
  change Φ p t - p.2 • (pathPrimitive hρ (pathSuperposition f hf.continuous (Φ p))) t = p.1 at pointwise
  rw [pathPrimitive_apply] at pointwise
  exact sub_eq_iff_eq_add.mp pointwise

end Burnett.Geometry.CotangentHamiltonInitialFamily
