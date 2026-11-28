import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicTest
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleParametricCyclic

set_option autoImplicit false
set_option maxRecDepth 6800
set_option maxHeartbeats 10800000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Analysis.ProjectiveNullCaps Burnett.V03 Burnett.V08
open Burnett.P01 (gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
  gaugeProjectionInfrared_zero gaugeProjectionInfrared_one)
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Interval Topology

abbrev WardParabolicTestPoint := E × NullCoordinateMap × ℝ × NullFrequencyCoordinates

private def wardParabolicTestDirection (p : WardParabolicTestPoint) : E :=
  p.2.1 (parabolicRemainder p.2.2.1 p.2.2.2)

private def wardParabolicTestSegment (p : WardParabolicTestPoint) (t : ℝ) : E :=
  p.2.2.2.1 • p.2.1 nullAxis + t • (p.2.2.1 • wardParabolicTestDirection p)

def wardParabolicTestDomain (ρ : ℝ) : Set WardParabolicTestPoint :=
  {p | ∀ t ∈ Icc (0 : ℝ) 1, ρ < ‖wardParabolicTestSegment p t‖}

def wardJointParabolicTestRemainder (a : Joint → ℝ) (p : WardParabolicTestPoint) : ℝ :=
  wardParabolicTestRemainder (fun ξ => a (p.1,ξ)) p.2.1 p.2.2.1 p.2.2.2

private theorem wardJoint_secondFDeriv_slice (b : Joint → ℝ) (hb : ContDiff ℝ ∞ b)
    (x y v w : E) :
    secondFDeriv (fun t => b (x,t)) y v w = secondFDeriv b (x,y) (0,v) (0,w) := by
  let I := ContinuousLinearMap.inr ℝ E E
  let S (z : E) := b (x,z)
  let L := ContinuousLinearMap.apply ℝ ℝ w
  let R := ContinuousLinearMap.apply ℝ ℝ ((0,w) : Joint)
  have incl (z : E) : HasFDerivAt (fun t : E => (x,t)) I z :=
    (hasFDerivAt_const x z).prodMk (hasFDerivAt_id z)
  have hS : ContDiff ℝ ∞ S := hb.comp (contDiff_const.prodMk contDiff_id)
  have hD (z : E) : fderiv ℝ S z = (fderiv ℝ b (x,z)).comp I :=
    ((hb.differentiable (by simp) (x,z)).hasFDerivAt.comp z (incl z)).fderiv
  have hf : (fun z : E => L (fderiv ℝ S z)) = (fun z => R (fderiv ℝ b (x,z))) := by
    funext z
    change fderiv ℝ S z w = fderiv ℝ b (x,z) (0,w)
    rw [hD]
    rfl
  have hSF : ContDiff ℝ ∞ (fderiv ℝ S) := hS.fderiv_right (by simp)
  have hBF : ContDiff ℝ ∞ (fderiv ℝ b) := hb.fderiv_right (by simp)
  have h₀ := L.hasFDerivAt.comp y ((hSF.differentiable (by simp) y).hasFDerivAt)
  have h₁ := (R.hasFDerivAt.comp (x,y)
    ((hBF.differentiable (by simp) (x,y)).hasFDerivAt)).comp y (incl y)
  change HasFDerivAt (fun z : E => L (fderiv ℝ S z)) (L.comp (secondFDeriv S y)) y at h₀
  rw [hf] at h₀
  have he := congrArg (fun D : E →L[ℝ] ℝ => D v) (h₀.unique h₁)
  exact he

private theorem wardParabolicTestDirection_smooth : ContDiff ℝ ∞ wardParabolicTestDirection := by
  let F (p : WardParabolicTestPoint) := p.2.1
  let δ (p : WardParabolicTestPoint) := p.2.2.1
  let u (p : WardParabolicTestPoint) := p.2.2.2
  have hF : ContDiff ℝ ∞ F := contDiff_fst.comp contDiff_snd
  have hδ : ContDiff ℝ ∞ δ := contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hu : ContDiff ℝ ∞ u := contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun p : WardParabolicTestPoint => parabolicRemainder (δ p) (u p)) :=
    contDiff_const.prodMk ((hδ.mul hu.snd.fst).prodMk hu.snd.snd)
  exact hF.clm_apply hv

private theorem wardParabolicTestSegment_smooth :
    ContDiff ℝ ∞ (fun q : WardParabolicTestPoint × ℝ => wardParabolicTestSegment q.1 q.2) := by
  let F (p : WardParabolicTestPoint) := p.2.1
  let δ (p : WardParabolicTestPoint) := p.2.2.1
  let s (p : WardParabolicTestPoint) := p.2.2.2.1
  have hF : ContDiff ℝ ∞ F := contDiff_fst.comp contDiff_snd
  have hδ : ContDiff ℝ ∞ δ := contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hs : ContDiff ℝ ∞ s := contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  exact ((hs.smul (hF.clm_apply contDiff_const)).comp contDiff_fst).add
    (contDiff_snd.smul ((hδ.smul wardParabolicTestDirection_smooth).comp contDiff_fst))

/-- The actual normalized near test has common smooth parameters for the
receiving center, cap frame, signed frequency, and cap width, including
zero width, on each uniformly separated interpolation window. -/
theorem exists_wardJointParabolicTestRemainder_extension (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ b : WardParabolicTestPoint → ℝ, ContDiff ℝ ∞ b ∧
      EqOn (wardJointParabolicTestRemainder a) b (wardParabolicTestDomain ρ) := by
  let b (x : Joint) := gaugeProjectionInfrared ((4/ρ) * ‖x.2‖) * a x
  have hOpen : IsOpen {x : Joint | x.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hb : ContDiff ℝ ∞ b := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x.2 = 0
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hn := (isOpen_lt (f := fun p : Joint => ‖p.2‖) continuous_snd.norm
        (continuous_const (y := ρ/4))).mem_nhds
        (show ‖x.2‖ < ρ/4 by rw [hx, norm_zero]; positivity)
      filter_upwards [hn] with y hy
      change ‖y.2‖ < ρ/4 at hy
      have h : (4/ρ) * ‖y.2‖ ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
        linarith only [hy]
      simp only [b, gaugeProjectionInfrared_zero h, zero_mul]
    · exact (gaugeProjectionInfrared_contDiff.contDiffAt.comp x
          (contDiffAt_const.mul (contDiffAt_snd.norm ℝ hx))).mul
        (ha.contDiffAt (hOpen.mem_nhds hx))
  have germ (x : E) (y : E) (hy : ρ < ‖y‖) :
      (fun ξ => b (x,ξ)) =ᶠ[𝓝 y] (fun ξ => a (x,ξ)) := by
    filter_upwards [(isOpen_lt (f := fun _ : E => ρ) continuous_const continuous_norm).mem_nhds hy] with ξ hξ
    change ρ < ‖ξ‖ at hξ
    have h : 2 ≤ (4/ρ) * ‖ξ‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
      linarith only [hξ, hρ]
    simp only [b, gaugeProjectionInfrared_one h, one_mul]
  let v (p : WardParabolicTestPoint × ℝ) : Joint := (0,wardParabolicTestDirection p.1)
  let s (p : WardParabolicTestPoint × ℝ) : Joint := (p.1.1,wardParabolicTestSegment p.1 p.2)
  let F (p : WardParabolicTestPoint × ℝ) := (1-p.2) * secondFDeriv b (s p) (v p) (v p)
  have hv : ContDiff ℝ ∞ v := contDiff_const.prodMk (wardParabolicTestDirection_smooth.comp contDiff_fst)
  have hs : ContDiff ℝ ∞ s := (contDiff_fst.comp contDiff_fst).prodMk wardParabolicTestSegment_smooth
  have hBF : ContDiff ℝ ∞ (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hB : ContDiff ℝ ∞ (secondFDeriv b) := hBF.fderiv_right (by simp)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_const.sub contDiff_snd).mul (((hB.comp hs).clm_apply hv).clm_apply hv)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, F (p,t), contDiff_unitIntervalIntegral F hF, ?_⟩
  intro p hp
  unfold wardJointParabolicTestRemainder wardParabolicTestRemainder
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hG := (germ p.1 (wardParabolicTestSegment p t) (hp t ht)).fderiv (𝕜 := ℝ)
  have hSecond : secondFDeriv (fun ξ => b (p.1,ξ)) (wardParabolicTestSegment p t) =
      secondFDeriv (fun ξ => a (p.1,ξ)) (wardParabolicTestSegment p t) := hG.fderiv_eq (𝕜 := ℝ)
  change (1-t) * secondFDeriv (fun ξ => a (p.1,ξ)) (wardParabolicTestSegment p t)
      (wardParabolicTestDirection p) (wardParabolicTestDirection p) = F (p,t)
  rw [← hSecond]
  exact congrArg (fun r : ℝ => (1-t) * r)
    (wardJoint_secondFDeriv_slice b hb p.1 (wardParabolicTestSegment p t)
      (wardParabolicTestDirection p) (wardParabolicTestDirection p))

theorem wardJointParabolicTestRemainder_contDiffOn (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (wardJointParabolicTestRemainder a) (wardParabolicTestDomain ρ) := by
  obtain ⟨b,hb,hEq⟩ := exists_wardJointParabolicTestRemainder_extension a ha ρ hρ
  exact hb.contDiffOn.congr hEq

end Burnett.C02
