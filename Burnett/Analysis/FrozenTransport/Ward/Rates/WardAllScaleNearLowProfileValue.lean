import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapValue
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearRadialCyclicity

set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Analysis.CapFourier
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

/-- The exact local low profile at normalized parabolic frequencies
agrees with the original branch at every common positive radial scale. -/
theorem wardNearLowProfile_value_at_scale {N : ℕ} (V : Set E) (G : E → Mat) (c : E)
    (hG : Matrix.det (G c) ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t * a (c,ξ))
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
    (hEncoded : ∀ x : NullFrequencyCoordinates, x.1 ≠ 0 →
      capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ (chartScaledFrequency F δ x) =
        parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ ci co vCap x)
    (j : WardNearEntries) (k : Fin 3) (u v : E) (l t : ℝ) (hl : 0 < l) (ht : 0 < t) :
    let A := capFrequencyEquiv F hδ
    let z : Joint := (A (l • u),A v)
    let x : WardNearProfileInput N :=
      (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),frequencyCoordinates u,frequencyCoordinates v,l)
    let sym := wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo hm hη ti thinOut
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (sym j) γ : Joint → ℂ)
    let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
    x ∈ wardParabolicNearProfileDomain N V tube d₀ (wardNearRotateCap k) →
    wardParabolicNearProfile G W M ϑ κ tube ti thinOut ci co false (wardNearRotateCap k)
      (wardNearRotateEntries k j) x = radianFourBranchSymbol ϑ κ (bases k) 0 (t • z) := by
  intro A z x sym μ bases hx
  let A' := (parabolicDilationEquiv hδ).trans F.toFrequency
  have hP : A' (l • frequencyCoordinates u) = z.1 := by rw [← map_smul]; rfl
  have hQ : A' (frequencyCoordinates v) = z.2 := rfl
  have hR : A' (-(l • frequencyCoordinates u+frequencyCoordinates v)) = -(z.1+z.2) := by
    rw [map_neg,map_add,hP,hQ]
  let P := capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ
  let f := wardParabolicNearProfile (N := N) G W M ϑ κ tube ti thinOut ci co false (wardNearRotateCap k)
    (wardNearRotateEntries k j)
  have hTest := wardParabolicNearProfile_eq_actual V G c hG a ha hOdd hHom d₀ M hM hMExact ϑ hCut κ
    hκ hκsmall tube δ ti thinOut ci co hδ hη γ F S.centers W wi wo hm hWide vCap hEncoded
    (frequencyCoordinates u) (frequencyCoordinates v) l hl false (by simp) (wardNearRotateCap k)
    (wardNearRotateEntries k j) hx
  change f x = ((δ^2)⁻¹ : ℝ) •
    ((P (![A' (l • frequencyCoordinates u),A' (frequencyCoordinates v),
        A' (-(l • frequencyCoordinates u+frequencyCoordinates v))] (wardNearRotateCap k)) : ℂ) *
      (lowSlotWeight ϑ κ (A' (l • frequencyCoordinates u)) (A' (frequencyCoordinates v))
        (A' (-(l • frequencyCoordinates u+frequencyCoordinates v))) : ℂ) *
      sym (wardNearRotateEntries k j) (A' (l • frequencyCoordinates u),A' (frequencyCoordinates v))) at hTest
  rw [hP,hQ,hR] at hTest
  have hScale := wardNear_rotatedLowBranch_normalize (G c) hG (fun ξ => a (c,ξ)) hHom ϑ κ δ wi wo
    hm hη ti thinOut ci co ce D S γ j k t ht z
  exact hTest.trans hScale.symm

end Burnett.C02
