import Burnett.Geometry.Cotangent.ScaledPicardPathIFT
import Burnett.Geometry.Cotangent.LocalFlowODEUniqueness

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The path-space equation yields the actual time derivative on the interior
of the fixed interval, including for zero and negative time scalings. -/
theorem hasDerivAt_clampedScaledPicardPath [CompleteSpace E] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (f : E → E) (hf : Continuous f) (x : E) (a : ℝ) (u : TimePath ρ E)
    (hu : ∀ t : Icc (-ρ) ρ,
      u t = x + a • ∫ s in (0 : ℝ)..(t : ℝ), f (u (projIcc (-ρ) ρ (by linarith) s)))
    {t : ℝ} (ht : t ∈ Ioo (-ρ) ρ) :
    HasDerivAt (fun s => u (projIcc (-ρ) ρ (by linarith) s))
      (a • f (u ⟨t, Ioo_subset_Icc_self ht⟩)) t := by
  let v (s : ℝ) := f (u (projIcc (-ρ) ρ (by linarith) s))
  have hcont : Continuous v := hf.comp (u.continuous.comp (continuous_projIcc (h := by linarith)))
  have hDeriv := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hDeriv' := (hDeriv.const_smul a).const_add x
  have ht' : t ∈ Icc (-ρ) ρ := Ioo_subset_Icc_self ht
  have hv : v t = f (u ⟨t, ht'⟩) := by
    change f (u (projIcc (-ρ) ρ (by linarith) t)) = _
    rw [projIcc_of_mem _ ht']
  rw [hv] at hDeriv'
  apply hDeriv'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  have hs' : s ∈ Icc (-ρ) ρ := Ioo_subset_Icc_self hs
  rw [projIcc_of_mem _ hs']
  exact hu ⟨s, hs'⟩

/-- Any genuine local flow of a smooth autonomous field is jointly smooth
near the initial point and zero time. Fixed path evaluation is compared with
the flow at the actual time by uniqueness on the whole rescaled interval. -/
theorem eventually_contDiffAt_actual_localFlow [CompleteSpace E] [ProperSpace E]
    {f : E → E} (hf : ContDiff ℝ ∞ f) {x₀ : E} {U : Set E} (hU : U ∈ 𝓝 x₀)
    {δ : ℝ} (hδ : 0 < δ) (Ψ : E × ℝ → E)
    (hinit : ∀ x ∈ U, Ψ (x, 0) = x)
    (hODE : ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => Ψ (x, s)) (f (Ψ (x, t))) t) :
    ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), ContDiffAt ℝ ∞ Ψ p := by
  obtain ⟨Φ, _, _, hΦ⟩ := exists_jointSmooth_scaledPicardPaths (ρ := 1) zero_le_one f hf x₀
  let R (p : E × ℝ) : E × ℝ := (p.1, 2 * p.2)
  have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hR₀ : R (x₀, 0) = (x₀, 0) := by simp [R]
  have hRt : Tendsto R (𝓝 (x₀, (0 : ℝ))) (𝓝 (x₀, (0 : ℝ))) := by
    have hRc : ContinuousAt R (x₀, (0 : ℝ)) := hR.continuous.continuousAt
    simpa only [hR₀] using hRc.tendsto
  let τ : Icc (-1 : ℝ) 1 := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
  let J : Set ℝ := Ioo (-1 : ℝ) 1
  have hzero : (0 : ℝ) ∈ J := by constructor <;> norm_num
  have hτ : (τ : ℝ) ∈ J := by constructor <;> norm_num [τ]
  let P (p : E × ℝ) : E := Φ (R p) τ
  have hSmoothP : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), ContDiffAt ℝ ∞ P p :=
    (hRt.eventually hΦ).mono fun p hp =>
      (ContinuousMap.evalCLM ℝ τ : TimePath 1 E →L[ℝ] E).contDiff.contDiffAt.comp p
        (hp.1.comp p hR.contDiffAt)
  have hNearU : ∀ᶠ p : E × ℝ in 𝓝 (x₀, (0 : ℝ)), p.1 ∈ U :=
    continuous_fst.continuousAt.preimage_mem_nhds hU
  have hNearT : ∀ᶠ p : E × ℝ in 𝓝 (x₀, (0 : ℝ)), |p.2| < δ / 2 :=
    continuous_snd.abs.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp; positivity))
  have hSame : P =ᶠ[𝓝 (x₀, (0 : ℝ))] Ψ := by
    filter_upwards [hRt.eventually hΦ, hNearU, hNearT] with p hp hx ht
    let a := 2 * p.2
    let W : TimePath 1 E := Φ (R p)
    let u (s : ℝ) := W (projIcc (-1 : ℝ) 1 (by norm_num) s)
    let v (s : ℝ) := Ψ (p.1, a * s)
    let rhs (y : E) := a • f y
    have hEq : ∀ t : Icc (-1 : ℝ) 1,
        W t = p.1 + a • ∫ s in (0 : ℝ)..(t : ℝ), f (u s) := hp.2
    have hu (s : ℝ) (hs : s ∈ J) : HasDerivAt u (rhs (u s)) s := by
      change HasDerivAt u (a • f (W (projIcc (-1 : ℝ) 1 (by norm_num) s))) s
      rw [projIcc_of_mem _ (Ioo_subset_Icc_self hs)]
      exact hasDerivAt_clampedScaledPicardPath zero_le_one f hf.continuous p.1 a W hEq hs
    have hv (s : ℝ) (hs : s ∈ J) : HasDerivAt v (rhs (v s)) s := by
      have hs' : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      have ha : |a * s| < δ := by
        calc
          |a * s| = (2 * |p.2|) * |s| := by simp [a, abs_mul]
          _ ≤ 2 * |p.2| := mul_le_of_le_one_right (by positivity) hs'
          _ < δ := by linarith
      have hODE' := hODE p.1 hx (a * s) (abs_lt.mp ha)
      simpa only [rhs, v, mul_one, Function.comp_def] using
        hODE'.scomp s ((hasDerivAt_id s).const_mul a)
    have h0 : u 0 = v 0 := by
      have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hzero
      change W (projIcc (-1 : ℝ) 1 (by norm_num) 0) = Ψ (p.1, a * 0)
      rw [projIcc_of_mem _ hz, hEq ⟨0, hz⟩]
      simp [hinit _ hx]
    have hLip : LocallyLipschitz rhs :=
      ((contDiff_const.smul hf : ContDiff ℝ ∞ rhs).of_le (by simp)).locallyLipschitz
    have eq := eqOn_autonomousSolutions_of_locallyLipschitz isOpen_Ioo
      (convex_Ioo (-1 : ℝ) 1).isPreconnected hzero hLip hu hv h0 hτ
    have hscale : a * (τ : ℝ) = p.2 := by
      change (2 * p.2) * (1 / 2) = p.2
      ring
    change W (projIcc (-1 : ℝ) 1 (by norm_num) τ) = Ψ (p.1, a * τ) at eq
    rw [projIcc_of_mem _ τ.property, hscale] at eq
    exact eq
  have hLocalEq : ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), P =ᶠ[𝓝 p] Ψ :=
    eventually_eventually_nhds.mpr hSame
  filter_upwards [hSmoothP, hLocalEq] with p hp he
  exact hp.congr_of_eventuallyEq he.symm

end Burnett.Geometry.CotangentHamiltonInitialFamily
