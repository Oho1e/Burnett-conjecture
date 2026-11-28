import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowProfileValue
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActiveProfileInputs
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileAxes

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Analysis.CapFourier
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

open private wardAxialDirection_lower from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileAxes

/-- The compact endpoint witness reads the original localized first-low
coefficient on all three actual enlarged-cap supports. Both a nonzero
physical ratio and the original cyclic cap placement are retained. -/
theorem wardNearLowProfileBinding {N : ℕ} (K V : Set E) (G : E → Mat) (c : E)
    (hG : Matrix.det (G c) ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t*a (c,ξ))
    (W : E → E → OrderedPair → OrderedPair → ℝ) (M : WardParabolicTestPoint → ℝ)
    (hM : ContDiff ℝ ∞ M) (d₀ : ℝ)
    (hMExact : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain d₀))
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (tube δ ti thinOut ci co ce D wi wo : ℝ) (hδ : δ ≠ 0) (hη : 0 < tube*δ^2)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (hWide : ∀ ξ, ∀ k j, W c ξ k j = (wideScreenAngular wi wo (inverseMatrix (G c)) hm).matrix ξ k j)
    (S : SmoothThinConeCaps (inverseMatrix (G c)) δ (tube*δ^2) ci co ce D) (γ : ↑S.centers)
    (F : NullCapChart (inverseMatrix (G c)) γ) (vCap : CapNeighborParameters N)
    (B Rv R ρMax s₀ e α L U b : ℝ)
    (hParam : ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) ∈ wardNearParameterCompact N K B Rv)
    (hEncoded : ∀ x : NullFrequencyCoordinates, x.1 ≠ 0 →
      capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ (chartScaledFrequency F δ x) =
        parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ ci co vCap x)
    (he : 0 < e) (heL : e ≤ L) (hα : 0 ≤ α) (hU : 0 < U)
    (hR : ‖frequencyCoordinates.toContinuousLinearMap‖ ≤ R)
    (hRatioMax : b*U/L ≤ ρMax) (hs₀ : s₀ ≤ α) (hs₀' : s₀ ≤ α*(L/(2*U)))
    (j : WardNearEntries) (k : Fin 3) (Fext : WardNearProfileInput N → ℂ) :
    let A := capFrequencyEquiv F hδ
    let Q := tsupport (enlargedCapMultiplier (inverseMatrix (G c)) δ (tube*δ^2) co ce γ)
    let T := wardNearProfileCompact N K B Rv R ρMax s₀
    let O := wardParabolicNearProfileDomain N V tube d₀ (wardNearRotateCap k)
    let f := wardParabolicNearProfile G W M ϑ κ tube ti thinOut ci co false (wardNearRotateCap k)
      (wardNearRotateEntries k j)
    let M₀ := wardNearEndpointProfile Fext e ((c,F.toFrequency.toContinuousLinearMap,δ),vCap)
    let sym := wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo hm hη ti thinOut
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (sym j) γ : Joint → ℂ)
    let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
    (∀ x g, (g ≠ 0 → x ∈ T) → (x ∈ O → f x = g) → Fext x = g) →
    (∀ p, A p ∈ Q → α*‖p‖ ≤ |p 0|) →
    (∀ p, ‖A p‖ ≤ U*‖p‖) →
    (∀ p, α*‖p‖ ≤ |(frequencyCoordinates p).1| → L*‖p‖ ≤ ‖A p‖) →
    ∀ p : Joint, A p.1 ∈ Q → A p.2 ∈ Q → A (-(p.1+p.2)) ∈ Q →
      ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b →
      (radianFourBranchSymbol ϑ κ (bases k) 0 ∘ pairedFrequencyEquiv A) p =
        M₀ (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖) := by
  intro A Q T O f M₀ sym μ bases hExtension hAxis hUp hLower p hpK hqK hrK hRho
  let y : Joint := (A p.1,A p.2)
  let g := radianFourBranchSymbol ϑ κ (bases k) 0 y
  let r := -(p.1+p.2)
  let u := endpointDirection p.1
  let v := endpointDirection p.2
  let l := ‖p.1‖/‖p.2‖
  let ρphys := ‖A p.1‖/‖A p.2‖
  let z : Joint := (A (l • u),A v)
  have hp : p.1 ≠ 0 := by
    intro h
    have e := hRho.1
    rw [h,A.map_zero,norm_zero,zero_div] at e
    exact (lt_irrefl _ e)
  have hq : p.2 ≠ 0 := by
    intro h
    have e := hRho.1
    rw [h,A.map_zero,norm_zero,div_zero] at e
    exact (lt_irrefl _ e)
  obtain ⟨hl,hUn,hVn,hYZ,hRatio⟩ := wardNear_normalizeEndpointRatio F hδ hp hq
  change ‖u‖ = 1 at hUn
  change ‖v‖ = 1 at hVn
  change wardParabolicRatioOfPhysical F.toFrequency.toContinuousLinearMap δ
    (frequencyCoordinates u) (frequencyCoordinates v) ρphys = l at hRatio
  have hUL : L ≤ ‖A u‖ := by
    apply (show L = L*‖u‖ by rw [hUn,mul_one]).trans_le
    apply hLower
    rw [hUn,mul_one]
    exact wardAxialDirection_lower hp (hAxis _ hpK)
  have hVL : L ≤ ‖A v‖ := by
    apply (show L = L*‖v‖ by rw [hVn,mul_one]).trans_le
    apply hLower
    rw [hVn,mul_one]
    exact wardAxialDirection_lower hq (hAxis _ hqK)
  let x : WardNearProfileInput N :=
    (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),frequencyCoordinates u,frequencyCoordinates v,l)
  have hInput : wardNearEndpointInput e ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) u v ρphys = x := by
    have hValue := wardNearEndpointInput_eq e he ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) u v ρphys
      (heL.trans hUL) (heL.trans hVL)
    exact hValue.trans (congrArg
      (fun R : ℝ => (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),frequencyCoordinates u,frequencyCoordinates v,R))
      hRatio)
  have hActive : g ≠ 0 → x ∈ T := by
    intro hg
    have hLow : lowSlotWeight ϑ κ (A p.1) (A p.2) (A r) ≠ 0 := by
      intro hz
      have hr : A r = -(A p.1+A p.2) := by simp only [r,map_neg,map_add]
      apply hg
      change (lowSlotWeight ϑ κ (A p.1) (A p.2) (-(A p.1+A p.2)) : ℂ) * bases k y = 0
      rw [← hr,hz,Complex.ofReal_zero,zero_mul]
    have h := wardNearLowEndpointCompact_mem F hδ c vCap B Rv R ρMax s₀ e α L U b hParam he heL hα hU
      hR hRatioMax hs₀ hs₀' ϑ hCut κ hκ hκsmall p.1 p.2 hp hq hUp hLower
      (hAxis _ hpK) (hAxis _ hqK) (hAxis _ hrK) hRho.2 hLow
    exact hInput ▸ h
  have hLocal : x ∈ O → f x = g := by
    intro hx
    have hValue := wardNearLowProfile_value_at_scale V G c hG a ha hOdd hHom W M hM d₀ hMExact
      ϑ hCut κ hκ hκsmall tube δ ti thinOut ci co ce D wi wo hδ hη hm hWide S γ F vCap hEncoded
      j k u v l ‖p.2‖ hl (norm_pos_iff.mpr hq) hx
    change y = ‖p.2‖ • z at hYZ
    exact hValue.trans (congrArg (radianFourBranchSymbol ϑ κ (bases k) 0) hYZ).symm
  have e' := hExtension x g hActive hLocal
  exact ((congrArg Fext hInput).trans e').symm

end Burnett.C02
