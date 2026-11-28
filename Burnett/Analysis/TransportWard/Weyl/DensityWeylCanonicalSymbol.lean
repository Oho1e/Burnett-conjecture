import Burnett.Analysis.TransportWard.Weyl.DensityWeylResidualBound
import Burnett.Analysis.TransportWard.Weyl.ActualCanonicalWeylLeading

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Filter Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.FirstOrderDyadic (baseDirectionSymbol)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff Topology BigOperators

local notation "J" => Fin 4 × Fin 4

/-- The fully assembled leading symbol is the canonical bracket everywhere.
On the actual Weyl window the coefficient germs give the same density
matrix. Off that window the Weyl test and both of its derivatives vanish. -/
theorem densityWeylLeadingSymbol_eq_canonicalBracket {ι : Type*}
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (θ : E → ℝ) (β : E → E → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (i j : ι)
    (hC : ∀ x ∈ tsupport θ, ∀ d : J,
      DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x)
    (hc : ∀ x ∈ tsupport θ, ∀ d : J, (fun y => c i j d y) =ᶠ[𝓝 x]
      fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) (x ξ : E) :
    let b := normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))
    densityWeylLeadingSymbol c b i j x ξ =
      (canonicalBracket (fun y q => frozenDensityPrincipalPhase S (G y) q i j)
        (fun y q => β y (WithLp.toLp 2 q)) x (physicalRadianCovector ξ) : ℂ) := by
  intro b
  by_cases hx : x ∈ tsupport θ
  · have hF : (∑ d : J, c i j d x * frozenSecondWeylLeading b d.1 d.2 x ξ) =
        frozenHessianTransportMatrix S (G x) b i j x ξ := by
      unfold frozenHessianTransportMatrix
      refine Finset.sum_congr rfl fun d _ => ?_
      exact congrArg (fun z : ℂ => z * frozenSecondWeylLeading b d.1 d.2 x ξ) (hc x hx d).self_of_nhds
    unfold densityWeylLeadingSymbol
    rw [Finset.sum_add_distrib,hF]
    exact variableDensityWeylLeading_eq_canonicalBracket S G c β hβ i j x ξ (hC x hx) (hc x hx)
  · have hZero (y : E) (hy : y ∉ tsupport θ) (ζ : E) : β y ζ = 0 := by
      by_contra hne
      exact zero_ne_one ((image_eq_zero_of_notMem_tsupport hy).symm.trans (hPlateau y ζ hne))
    have hB (y : E) (hy : y ∉ tsupport θ) (ν : E) : b y ν = 0 := by
      change (β y (tau • ν) : ℂ) = 0
      rw [hZero y hy,Complex.ofReal_zero]
    have hb (e : E) : baseDirectionSymbol b e x ξ = 0 :=
      baseDirectionSymbol_eq_zero_off_closed (isClosed_tsupport θ) hB e hx
    have hL : densityWeylLeadingSymbol c b i j x ξ = 0 := by
      unfold densityWeylLeadingSymbol
      refine Finset.sum_eq_zero fun d _ => ?_
      simp only [frozenSecondWeylLeading,variableSecondWeylLeading,hb,
        coefficientCommutatorLeading_eq_zero_of_zero_row (c i j d) (hB x hx),mul_zero,add_zero]
    let test (y : E) (q : Covector) := β y (WithLp.toLp 2 q)
    let p := physicalRadianCovector ξ
    have hTestBase : (fun y => test y p) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport θ).isOpen_compl.mem_nhds hx] with y hy
      exact hZero y hy _
    have hTestFiber : test x = fun _ => 0 := funext (fun q => hZero x hx _)
    have hBase (k : Fin 4) : basePartial k test x p = 0 := by
      rw [basePartial,hTestBase.fderiv_eq,fderiv_const_apply,ContinuousLinearMap.zero_apply]
    have hFiber (k : Fin 4) : momentumPartial k test x p = 0 := by
      rw [momentumPartial,hTestFiber,fderiv_const_apply,ContinuousLinearMap.zero_apply]
    have hCan (A : E → Covector → ℝ) : canonicalBracket A test x p = 0 := by
      simp only [canonicalBracket,hBase,hFiber,mul_zero,sub_zero,Finset.sum_const_zero]
    change _ = (canonicalBracket _ test x p : ℂ)
    rw [hCan,Complex.ofReal_zero]
    exact hL

end Burnett.V03.Palatini
