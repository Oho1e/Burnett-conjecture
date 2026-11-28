import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowScreenedCore

set_option autoImplicit false
set_option maxRecDepth 8200
set_option maxHeartbeats 11000000

noncomputable section

namespace Burnett.C02

open Set
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.CapFourier (parabolicDilationEquiv)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

open private wardParabolicLowCoreAmplitude wardLowCoreScreenPoint wardLowCoreThirdInput from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowScreenedCore

/-- At genuine nonzero cap width and low ratio, the smooth normalized
kernel has the same three original thin screen columns in the three
physical slots of the Fourier vertex. -/
theorem wardParabolicLowScreenedCore_eq_actual
    (G : E → Mat) (a : Joint → ℝ) (c : E) (hG : Matrix.det (G c) ≠ 0)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t * a (c,ξ))
    (ρ₀ : ℝ) (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (hExt : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain ρ₀))
    (w : E) (F : NullCapChart (inverseMatrix (G c)) w)
    (W : E → E → OrderedPair → OrderedPair → ℝ) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (hWide : ∀ ξ, ∀ k j, W c ξ k j = (wideScreenAngular wi wo (inverseMatrix (G c)) hm).matrix ξ k j)
    (tube δ inn out : ℝ) (hδ : δ ≠ 0) (hη : 0 < tube * δ^2)
    (u₀ θ : NullFrequencyCoordinates) (ρ : ℝ) (hρ : 0 < ρ)
    (hu₀ : u₀.1 ≠ 0) (hθ : θ.1 ≠ 0) (hv : (θ + ρ • u₀).1 ≠ 0)
    (hu₀D : (c,F.toFrequency.toContinuousLinearMap,δ,u₀) ∈ wardParabolicTestDomain ρ₀)
    (hθD : (c,F.toFrequency.toContinuousLinearMap,δ,θ) ∈ wardParabolicTestDomain ρ₀)
    (hvD : (c,F.toFrequency.toContinuousLinearMap,δ,θ+ρ • u₀) ∈ wardParabolicTestDomain ρ₀)
    (k j l : OrderedPair) :
    let A := (parabolicDilationEquiv hδ).trans F.toFrequency
    let p := A (ρ • u₀)
    let q := A θ
    let r := A (-(ρ • u₀ + θ))
    let S := thinScreenAngular (inverseMatrix (G c)) wi wo hm hη inn out
    let H (i j : Fin 4) := S.complex p (i,j) k
    let J (i j' : Fin 4) := S.complex q (i,j') j
    let L (i j : Fin 4) := S.complex r (i,j) l
    let Γ := complexPrincipalVertex (G c) (fun i => p i) H (fun i => q i) J (fun i => r i) L
    ((a (c,p)+a (c,q)+a (c,r) : ℝ) : ℂ) * Γ / ((δ^2 * (‖p‖ * ‖q‖ * ‖r‖) : ℝ) : ℂ) =
      wardParabolicLowScreenedCore G W M tube inn out k j l ((c,F.toFrequency.toContinuousLinearMap,δ),u₀,θ,ρ) := by
  intro A p q r S H J L Γ
  let v := θ+ρ • u₀
  let P (u : NullFrequencyCoordinates) : WardParabolicTestPoint := (c,F.toFrequency.toContinuousLinearMap,δ,u)
  have hρP : p = ρ • A u₀ := A.map_smul ρ u₀
  have hvP : r = -(A v) := by
    change A (-(ρ • u₀ + θ)) = -(A (θ+ρ • u₀))
    rw [add_comm (ρ • u₀) θ, map_neg]
  have one (u : NullFrequencyCoordinates) (k : OrderedPair) :
      wardParabolicLowCoreAmplitude W tube inn out k (P u) =
        fun i j => ((S.matrix (A u) (i,j) k : ℝ) : ℂ) := by
    funext i j
    change (wardParabolicThinScreenEntry W tube inn out (i,j) k (P u) : ℂ) =
      (S.matrix (A u) (i,j) k : ℂ)
    exact congrArg Complex.ofReal
      (wardParabolicThinScreenEntry_eq_actual (inverseMatrix (G c)) w F W c wi wo hm hWide
        tube δ inn out hδ hη u (i,j) k)
  have hH : (wardParabolicLowCoreAmplitude W tube inn out k (P u₀) : ComplexTensor2) = H := by
    rw [one]
    funext i j'
    change (S.matrix (A u₀) (i,j') k : ℂ) = (S.matrix p (i,j') k : ℂ)
    rw [hρP, S.degree ρ hρ]
  have hJ : (wardParabolicLowCoreAmplitude W tube inn out j (P θ) : ComplexTensor2) = J := one θ j
  have hL : (wardParabolicLowCoreAmplitude W tube inn out l (P v) : ComplexTensor2) = L := by
    rw [one]
    funext i j'
    change (S.matrix (A v) (i,j') l : ℂ) = (S.matrix r (i,j') l : ℂ)
    rw [hvP, thinScreenAngular_even _ _ _ hm hη inn out]
  have e := wardParabolicLowNormalizedKernel_eq (G c) hG a ha c hOdd hHom ρ₀ M hM hExt
    F.toFrequency δ hδ u₀ θ ρ 1 hρ zero_lt_one hu₀ hθ
    (by simpa only [div_one] using hv) hu₀D hθD (by simpa only [div_one] using hvD) H J L
  dsimp only at e
  simp only [one_smul, div_one] at e
  refine e.trans ?_
  change _ = ((wardParabolicLowCyclicTest M ((c,F.toFrequency.toContinuousLinearMap,δ),u₀,θ,ρ) : ℝ) : ℂ) *
    complexPrincipalVertex (G c) (fun i => (ρ • A u₀) i) (wardParabolicLowCoreAmplitude W tube inn out k (P u₀))
      (fun i => A θ i) (wardParabolicLowCoreAmplitude W tube inn out j (P θ))
      (fun i => (-A v) i) (wardParabolicLowCoreAmplitude W tube inn out l (P v)) *
       ((((‖A u₀‖ * ‖A θ‖ * ‖A v‖)⁻¹ : ℝ)) : ℂ)
  rw [hH,hJ,hL,div_eq_mul_inv,Complex.ofReal_inv]
  rw [← A.map_smul]
  rfl

end Burnett.C02
