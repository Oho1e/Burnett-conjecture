import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth
import Burnett.Analysis.AngularCaps.CapFrequencyCoordinates

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 8500000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.Analysis.ProjectiveNullCaps Burnett.V08
open Burnett.Analysis.CapFourier (parabolicDilationEquiv)
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Interval

abbrev WardParabolicBase := E × NullCoordinateMap × ℝ
abbrev WardParabolicLowTestPoint :=
  WardParabolicBase × NullFrequencyCoordinates × NullFrequencyCoordinates × ℝ

def wardParabolicTestSlice (M : WardParabolicTestPoint → ℝ) (c : WardParabolicBase)
    (u : NullFrequencyCoordinates) : ℝ :=
  M (c.1,c.2.1,c.2.2,u)

/-- Extend the normalized low-first cyclic coefficient to zero radial
ratio by integrating the actual frequency derivative along the high ray. -/
def wardParabolicLowCyclicTest (M : WardParabolicTestPoint → ℝ) (x : WardParabolicLowTestPoint) : ℝ :=
  let B := wardParabolicTestSlice M x.1
  let u₀ := x.2.1
  let θ := x.2.2.1
  let ρ := x.2.2.2
  B u₀ - ∫ t in (0 : ℝ)..1, fderiv ℝ B (θ + t • (ρ • u₀)) u₀

theorem wardParabolicLowCyclicTest_smooth (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (wardParabolicLowCyclicTest M) := by
  let X := WardParabolicLowTestPoint
  let chartInput (p : X) (u : NullFrequencyCoordinates) : WardParabolicTestPoint :=
    (p.1.1,p.1.2.1,p.1.2.2,u)
  let L : NullFrequencyCoordinates →L[ℝ] WardParabolicTestPoint :=
    (0 : NullFrequencyCoordinates →L[ℝ] E).prod
      ((0 : NullFrequencyCoordinates →L[ℝ] NullCoordinateMap).prod
        ((0 : NullFrequencyCoordinates →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ NullFrequencyCoordinates)))
  have hSlice (p : X) (u : NullFrequencyCoordinates) :
      fderiv ℝ (wardParabolicTestSlice M p.1) u = (fderiv ℝ M (chartInput p u)).comp L := by
    have hF : HasFDerivAt (chartInput p) L u :=
      (hasFDerivAt_const p.1.1 u).prodMk ((hasFDerivAt_const p.1.2.1 u).prodMk
        ((hasFDerivAt_const p.1.2.2 u).prodMk (hasFDerivAt_id u)))
    exact ((hM.differentiable (by simp) (chartInput p u)).hasFDerivAt.comp u hF).fderiv
  let u₀ (p : X) := p.2.1
  let θ (p : X) := p.2.2.1
  let ρ (p : X) := p.2.2.2
  have hu₀ : ContDiff ℝ ∞ u₀ := contDiff_fst.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ θ := contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hρ : ContDiff ℝ ∞ ρ := contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hp (u : X → NullFrequencyCoordinates) (hu : ContDiff ℝ ∞ u) :
      ContDiff ℝ ∞ (fun p => chartInput p (u p)) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk hu))
  let Y (p : X × ℝ) : WardParabolicTestPoint := chartInput p.1 (θ p.1 + p.2 • (ρ p.1 • u₀ p.1))
  have hY : ContDiff ℝ ∞ Y :=
    ((contDiff_fst.fst.fst).prodMk ((contDiff_fst.fst.snd.fst).prodMk ((contDiff_fst.fst.snd.snd).prodMk
      ((hθ.comp contDiff_fst).add (contDiff_snd.smul ((hρ.smul hu₀).comp contDiff_fst))))))
  let F (p : X × ℝ) := (fderiv ℝ M (Y p)) (L (u₀ p.1))
  have hF : ContDiff ℝ ∞ F := ((hM.fderiv_right (by simp)).comp hY).clm_apply
    (L.contDiff.comp (hu₀.comp contDiff_fst))
  have hSmooth : ContDiff ℝ ∞ (fun p : X => M (chartInput p (u₀ p)) - ∫ t in (0 : ℝ)..1, F (p,t)) :=
    (hM.comp (hp u₀ hu₀)).sub (contDiff_unitIntervalIntegral F hF)
  have hEq : (fun p : X => M (chartInput p (u₀ p)) - ∫ t in (0 : ℝ)..1, F (p,t)) = wardParabolicLowCyclicTest M := by
    funext p
    unfold wardParabolicLowCyclicTest
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    change F (p,t) = (fderiv ℝ (wardParabolicTestSlice M p.1) (θ p + t • (ρ p • u₀ p))) (u₀ p)
    rw [hSlice]
    rfl
  exact hEq ▸ hSmooth

private theorem wardParabolicLowCyclicTest_endpoint (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (c : WardParabolicBase) (u₀ θ : NullFrequencyCoordinates) (ρ : ℝ) :
    let B := wardParabolicTestSlice M c
    ρ * wardParabolicLowCyclicTest M (c,u₀,θ,ρ) = ρ * B u₀ - (B (θ + ρ • u₀) - B θ) := by
  intro B
  have hB : ContDiff ℝ ∞ B := hM.comp
    (contDiff_const.prodMk (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))
  let g (t : ℝ) := B (θ + t • (ρ • u₀))
  let g' (t : ℝ) := ρ * (fderiv ℝ B (θ + t • (ρ • u₀))) u₀
  have hg' : Continuous g' := by
    have hp : ContDiff ℝ ∞ (fun t : ℝ => θ + t • (ρ • u₀)) := contDiff_const.add (contDiff_id.smul contDiff_const)
    exact (continuous_const.mul ((((hB.fderiv_right (by simp)).comp hp).clm_apply contDiff_const).continuous))
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun s : ℝ => θ + s • (ρ • u₀)) (ρ • u₀) t := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (ρ • u₀)).const_add θ
    have hd := ((hB.differentiable (by simp) (θ+t • (ρ • u₀))).hasFDerivAt.comp_hasDerivAt t hp)
    simpa only [g, g', map_smul, smul_eq_mul] using hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) (hg'.intervalIntegrable 0 1)
  change ρ * (B u₀ - ∫ t in (0 : ℝ)..1, (fderiv ℝ B (θ + t • (ρ • u₀))) u₀) = _
  rw [mul_sub, ← intervalIntegral.integral_const_mul]
  change ρ * B u₀ - (∫ t in (0 : ℝ)..1, g' t) = _
  rw [hFTC]
  simp only [g, one_smul, zero_smul, add_zero]

/-- The actual near test equals `δ²` times the low radial frequency
times one smooth normalized coefficient, with no division in that coefficient. -/
theorem wardParabolicLowCyclicTest_eq_original (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (c : E)
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t * a (c,ξ))
    (ρ₀ : ℝ) (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (hExt : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain ρ₀))
    (F : NullFrequencyCoordinates ≃L[ℝ] E) (δ : ℝ) (hδ : δ ≠ 0)
    (u₀ θ : NullFrequencyCoordinates) (l h : ℝ) (hl : 0 < l) (hh : 0 < h)
    (hu₀ : u₀.1 ≠ 0) (hθ : θ.1 ≠ 0) (hv : (θ+(l/h) • u₀).1 ≠ 0)
    (hu₀D : (c,F.toContinuousLinearMap,δ,u₀) ∈ wardParabolicTestDomain ρ₀)
    (hθD : (c,F.toContinuousLinearMap,δ,θ) ∈ wardParabolicTestDomain ρ₀)
    (hvD : (c,F.toContinuousLinearMap,δ,θ+(l/h) • u₀) ∈ wardParabolicTestDomain ρ₀) :
    let A := (parabolicDilationEquiv hδ).trans F
    a (c,A (l • u₀)) + a (c,A (h • θ)) + a (c,A (-(l • u₀+h • θ))) =
      δ^2 * l * wardParabolicLowCyclicTest M ((c,F.toContinuousLinearMap,δ),u₀,θ,l/h) := by
  intro A
  let v := θ+(l/h) • u₀
  let B := (c,F.toContinuousLinearMap,δ)
  let U := wardParabolicTestSlice M B
  let b (ξ : E) := a (c,ξ)
  have hb : ContDiffOn ℝ ∞ b {ξ : E | ξ ≠ 0} :=
    ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)
  have hlh : h * (l/h) = l := by field_simp
  have hV : h • A v = l • A u₀ + h • A θ := by
    simp only [v, map_add, map_smul, smul_add, smul_smul, hlh]
    rw [add_comm]
  have hR : A (-(l • u₀+h • θ)) = -(h • A v) := by rw [map_neg, map_add, map_smul, map_smul, hV]
  let L := fderiv ℝ b (F nullAxis)
  have hLinear : h * L (A v) = l * L (A u₀) + h * L (A θ) := by
    have h' := congrArg L hV
    simpa only [map_add, map_smul, smul_eq_mul] using h'
  have hRemainder (u : NullFrequencyCoordinates) (hu : u.1 ≠ 0)
      (hD : (c,F.toContinuousLinearMap,δ,u) ∈ wardParabolicTestDomain ρ₀) :
      b (A u) - L (A u) = δ^2 * U u := by
    have h := wardParabolicTestRemainder_eq b hb hOdd hHom F δ u hu
    change b (A u) - L (A u) = δ^2 * (wardJointParabolicTestRemainder a (c,F.toContinuousLinearMap,δ,u)) at h
    rwa [hExt hD] at h
  have h₀ := hRemainder u₀ hu₀ hu₀D
  have h₁ := hRemainder θ hθ hθD
  have h₂ := hRemainder v hv hvD
  have hC := wardParabolicLowCyclicTest_endpoint M hM B u₀ θ (l/h)
  change (l/h) * wardParabolicLowCyclicTest M (B,u₀,θ,l/h) = (l/h) * U u₀ - (U v - U θ) at hC
  have hScaled : l * wardParabolicLowCyclicTest M (B,u₀,θ,l/h) = l * U u₀ + h * U θ - h * U v := by
    calc
      _ = h * ((l/h) * wardParabolicLowCyclicTest M (B,u₀,θ,l/h)) := by rw [← mul_assoc,hlh]
      _ = _ := by rw [hC, mul_sub, ← mul_assoc, hlh]; ring
  rw [hR, map_smul, map_smul, hOdd, hHom l hl, hHom h hh, hHom h hh]
  change l * b (A u₀) + h * b (A θ) - h * b (A v) =
    δ^2 * l * wardParabolicLowCyclicTest M (B,u₀,θ,l/h)
  linear_combination l * h₀ + h * h₁ - h * h₂ - hLinear - δ^2 * hScaled

end Burnett.C02
