import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowCyclicTest
import Burnett.Analysis.TransportWard.ComplexWard

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 8900000

noncomputable section

namespace Burnett.C02

open Set
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.CapFourier (parabolicDilationEquiv)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol
open scoped ContDiff

/-- The near-low normalized cubic kernel keeps the exact three Euclidean
lengths and the genuine complex action vertex. The amplitudes can be the
actual original screen of any three ordered tensor inputs. -/
theorem wardParabolicLowNormalizedKernel_eq (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (c : E)
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t * a (c,ξ))
    (ρ₀ : ℝ) (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (hExt : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain ρ₀))
    (F : NullFrequencyCoordinates ≃L[ℝ] E) (δ : ℝ) (hδ : δ ≠ 0)
    (u₀ θ : NullFrequencyCoordinates) (l h : ℝ) (hl : 0 < l) (hh : 0 < h)
    (hu₀ : u₀.1 ≠ 0) (hθ : θ.1 ≠ 0) (hv : (θ+(l/h) • u₀).1 ≠ 0)
    (hu₀D : (c,F.toContinuousLinearMap,δ,u₀) ∈ wardParabolicTestDomain ρ₀)
    (hθD : (c,F.toContinuousLinearMap,δ,θ) ∈ wardParabolicTestDomain ρ₀)
    (hvD : (c,F.toContinuousLinearMap,δ,θ+(l/h) • u₀) ∈ wardParabolicTestDomain ρ₀)
    (H J L : ComplexTensor2) :
    let A := (parabolicDilationEquiv hδ).trans F
    let v := θ+(l/h) • u₀
    let p := A (l • u₀)
    let q := A (h • θ)
    let r := A (-(l • u₀+h • θ))
    let Γ := complexPrincipalVertex G (fun i => p i) H (fun i => q i) J (fun i => r i) L
    let Γ' := complexPrincipalVertex G (fun i => A ((l/h) • u₀) i) H (fun i => A θ i) J
      (fun i => -A v i) L
    let β := wardParabolicLowCyclicTest M ((c,F.toContinuousLinearMap,δ),u₀,θ,l/h)
    ((a (c,p)+a (c,q)+a (c,r) : ℝ) : ℂ) * Γ / ((δ^2 * (‖p‖ * ‖q‖ * ‖r‖) : ℝ) : ℂ) =
      ((β : ℂ) * Γ') / ((‖A u₀‖ * ‖A θ‖ * ‖A v‖ : ℝ) : ℂ) := by
  intro A v p q r Γ Γ' β
  have hα : a (c,p)+a (c,q)+a (c,r) = δ^2 * l * β :=
    wardParabolicLowCyclicTest_eq_original a ha c hOdd hHom ρ₀ M hM hExt F δ hδ u₀ θ l h
      hl hh hu₀ hθ hv hu₀D hθD hvD
  have hlh : h * (l/h) = l := by field_simp
  have hp : p = h • A ((l/h) • u₀) := by
    dsimp only [p]
    rw [← map_smul, smul_smul, hlh]
  have hq : q = h • A θ := A.map_smul h θ
  have hvA : h • A v = p+q := by
    simp only [v, p, q, map_add, map_smul, smul_add, smul_smul, hlh]
    rw [add_comm]
  have hr : r = h • (-A v) := by
    rw [smul_neg, hvA]
    exact (A.map_neg _).trans (congrArg Neg.neg (A.map_add _ _))
  have hΓ : Γ = ((h^2 : ℝ) : ℂ) * Γ' := by
    change complexPrincipalVertex G (fun i => p i) H (fun i => q i) J (fun i => r i) L = _
    rw [hp,hq,hr]
    simpa only [Complex.ofReal_pow] using (complexPrincipalVertex_frequency_homogeneity G hG
      (fun i => A ((l/h) • u₀) i) (fun i => A θ i) (fun i => -A v i) H J L h)
  let X := ‖A u₀‖ * ‖A θ‖ * ‖A v‖
  have hNorm : ‖p‖ * ‖q‖ * ‖r‖ = (l*h^2) * X := by
    rw [show p = l • A u₀ from A.map_smul l u₀, hq, hr]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hl, abs_of_pos hh, norm_neg, X]
    ring
  have hBase : ((δ^2 * (l * h^2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ hδ) (mul_ne_zero hl.ne' (pow_ne_zero _ hh.ne')))
  rw [hα,hΓ,hNorm]
  calc
    _ = (((δ^2 * (l*h^2) : ℝ) : ℂ) * ((β : ℂ) * Γ')) /
        (((δ^2 * (l*h^2) : ℝ) : ℂ) * (X : ℂ)) := by push_cast; ring
    _ = _ := mul_div_mul_left _ _ hBase

end Burnett.C02
