import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapValue
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActiveProfileInputs

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3700000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

/-- The comparable-box witness agrees at every actual pair of annular
inputs. A nonzero coefficient forces the third covector onto the same
enlarged cap before the compact extension is used. -/
theorem wardNearComparableProfileBinding {N : ℕ} (K V : Set E) (G : E → Mat) (c : E)
    (hG : Matrix.det (G c) ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t*a (c,ξ))
    (W : E → E → OrderedPair → OrderedPair → ℝ) (M : WardParabolicTestPoint → ℝ)
    (hM : ContDiff ℝ ∞ M) (d₀ : ℝ)
    (hMExact : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain d₀))
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (tube δ ti thinOut ci co ce D wi wo : ℝ) (hδ : δ ≠ 0) (hη : 0 < tube*δ^2)
    (hti : 0 ≤ ti) (hThin : ti < thinOut)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (hWide : ∀ ξ, ∀ k j, W c ξ k j = (wideScreenAngular wi wo (inverseMatrix (G c)) hm).matrix ξ k j)
    (S : SmoothThinConeCaps (inverseMatrix (G c)) δ (tube*δ^2) ci co ce D) (γ : ↑S.centers)
    (F : NullCapChart (inverseMatrix (G c)) γ) (vCap : CapNeighborParameters N)
    (B Rv R ρMax s₀ α L U : ℝ)
    (hParam : ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) ∈ wardNearParameterCompact N K B Rv)
    (hEncoded : ∀ x : NullFrequencyCoordinates, x.1 ≠ 0 →
      capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ (chartScaledFrequency F δ x) =
        parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ ci co vCap x)
    (hρMax : 1 ≤ ρMax) (hα : 0 < α) (hL : 0 < L) (hU : 0 < U)
    (hs₀ : s₀ ≤ min (α/2) (α*(κ*L/(4*U))))
    (j : WardNearEntries) (Fext : WardNearProfileInput N → ℂ) (k : ℤ) (ζ υ : E)
    (hRadial : endpointHighProfile υ ≠ 0)
    (hζ : ‖frequencyCoordinates ((2 : ℝ)^k • ζ)‖ ≤ R) (hυ : ‖frequencyCoordinates υ‖ ≤ R) :
    let A := capFrequencyEquiv F hδ
    let P := capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ
    let Pplus := enlargedCapMultiplier (inverseMatrix (G c)) δ (tube*δ^2) co ce γ
    let T := wardNearProfileCompact N K B Rv R ρMax s₀
    let O := wardParabolicNearProfileDomain N V tube d₀ 0
    let f := wardParabolicNearProfile G W M ϑ κ tube ti thinOut ci co true 0 j
    let sym := wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo hm hη ti thinOut j
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S sym γ : Joint → ℂ)
    (∀ x g, (g ≠ 0 → x ∈ T) → (x ∈ O → f x = g) → Fext x = g) →
    (∀ p, p ∈ tsupport Pplus → α*‖A.symm p‖ ≤ |(frequencyCoordinates (A.symm p)).1|) →
    (∀ p, ‖A p‖ ≤ U*‖p‖) →
    (∀ p, α*‖p‖ ≤ |(frequencyCoordinates p).1| → L*‖p‖ ≤ ‖A p‖) →
    (∀ y : Joint, sym y ≠ 0 → P y.1 ≠ 0 →
      Pplus y.1 = 1 ∧ Pplus y.2 = 1 ∧ Pplus (-(y.1+y.2)) = 1) →
    wardNearComparableBoxProfile Fext ((c,F.toFrequency.toContinuousLinearMap,δ),vCap) k (joinedInputs ζ υ) =
      (radianFourBranchSymbol ϑ κ μ 3 ∘ pairedFrequencyEquiv A) ((2 : ℝ)^k • ζ,υ) := by
  intro A P Pplus T O f sym μ hExtension hAxis hUp hLower hPlateaux
  let u := (2 : ℝ)^k • ζ
  let v := υ
  let r := -(u+v)
  let y : Joint := (A u,A v)
  let g := radianFourBranchSymbol ϑ κ μ 3 y
  let x : WardNearProfileInput N :=
    (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),frequencyCoordinates u,frequencyCoordinates v,1)
  have e : A r = -(A u+A v) := by simp only [r,map_neg,map_add]
  have hExpr : g = (comparableSlotWeight ϑ κ (A u) (A v) (A r) : ℂ) *
      (((δ^2)⁻¹ : ℝ) • ((P (A u) : ℂ)*sym y)) := by
    rw [e]
    rfl
  have hAx (p : E) (hp : Pplus (A p) = 1) :
      α*‖p‖ ≤ |(frequencyCoordinates p).1| := by
    have hn : Pplus (A p) ≠ 0 := by rw [hp]; exact one_ne_zero
    have e' := hAxis (A p) (subset_tsupport Pplus hn)
    rwa [A.symm_apply_apply] at e'
  have hActive : g ≠ 0 → x ∈ T := by
    intro hg
    have hmNZ : sym y ≠ 0 := by
      intro hz
      exact hg (by rw [hExpr,hz,mul_zero,smul_zero,mul_zero])
    have hP : P (A u) ≠ 0 := by
      intro hz
      exact hg (by rw [hExpr,hz,Complex.ofReal_zero,zero_mul,smul_zero,mul_zero])
    have hC : comparableSlotWeight ϑ κ (A u) (A v) (A r) ≠ 0 := by
      intro hz
      exact hg (by rw [hExpr,hz,Complex.ofReal_zero,zero_mul])
    obtain ⟨hp,hq,hr,_⟩ := wardNearGradientSymbol_support (G c) hG (fun ξ => a (c,ξ)) ϑ κ δ wi wo
      hm hη ti thinOut hti hThin j y hmNZ
    have hr' : A r ≠ 0 := e.symm ▸ hr
    obtain ⟨h₀,h₁,h₂⟩ := hPlateaux y hmNZ hP
    have hb₀ := hAx u h₀
    have hb₁ := hAx v h₁
    have hb₂ := hAx r (by rw [e]; exact h₂)
    exact wardNearComparableBoxCompact_mem F hδ c vCap B Rv R ρMax s₀ α L U hParam hρMax hα hL hU
      ϑ hCut hFlat κ hκ hκsmall hs₀ u v hζ hυ (endpointHighProfile_properties.2.2 υ hRadial).1.le
      hUp (hLower v hb₁) hb₀ hb₁ hb₂ hp hr' hC
  have hLocal : x ∈ O → f x = g := by
    intro hx
    let A' := (parabolicDilationEquiv hδ).trans F.toFrequency
    have hP : A' ((1:ℝ) • frequencyCoordinates u) = A u := by rw [one_smul]; rfl
    have hQ : A' (frequencyCoordinates v) = A v := rfl
    have hR : A' (-((1:ℝ) • frequencyCoordinates u+frequencyCoordinates v)) = A r := by
      rw [map_neg,map_add,hP,hQ,e]
    have hValue := wardParabolicNearProfile_eq_actual V G c hG a ha hOdd hHom d₀ M hM hMExact ϑ hCut κ
      hκ hκsmall tube δ ti thinOut ci co hδ hη γ F S.centers W wi wo hm hWide vCap hEncoded
      (frequencyCoordinates u) (frequencyCoordinates v) 1 zero_lt_one true (fun _ => rfl) 0 j hx
    change f x = ((δ^2)⁻¹ : ℝ) • ((P (A' ((1:ℝ) • frequencyCoordinates u)) : ℂ) *
      (comparableSlotWeight ϑ κ (A' ((1:ℝ) • frequencyCoordinates u)) (A' (frequencyCoordinates v))
        (A' (-((1:ℝ) • frequencyCoordinates u+frequencyCoordinates v))) : ℂ) *
      sym (A' ((1:ℝ) • frequencyCoordinates u),A' (frequencyCoordinates v))) at hValue
    rw [hP,hQ,hR] at hValue
    rw [hValue,hExpr]
    simp only [Complex.real_smul,y]
    ring
  change Fext (((c,F.toFrequency.toContinuousLinearMap,δ),vCap),
    frequencyCoordinates ((2 : ℝ)^k • firstInput (joinedInputs ζ υ)),
    frequencyCoordinates (secondInput (joinedInputs ζ υ)),1) = g
  rw [firstInput_joined,secondInput_joined]
  exact hExtension x g hActive hLocal

end Burnett.C02
