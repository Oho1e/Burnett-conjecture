import Burnett.Analysis.TransportWard.Weyl.ActualDensityVariableLeading

/-! The negative coordinate contraction is the canonical base derivative
term of the same variable normalized density Hessian. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 4100

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped BigOperators ContDiff Topology

local notation "J" => Fin 4 × Fin 4

theorem actualDensityPhase_basePartial {ι : Type*} (S : ι → Mat) (G : E → Mat)
    (i j : ι) (k : Fin 4) (x : E) (p : Covector)
    (hC : ∀ d : J, DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x) :
    basePartial k (fun y q => frozenDensityPrincipalPhase S (G y) q i j) x p =
      ∑ d : J, (p d.1 * p d.2) *
        fderiv ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x (coordinateDirection k) := by
  let C (a b : Fin 4) (y : E) := metricActionCoefficient S (a,i) (b,j) (G y)
  let e := coordinateDirection k
  have hd (a b : Fin 4) : HasFDerivAt (fun y => C a b y * (p a * p b))
      ((p a * p b) • fderiv ℝ (C a b) x) x :=
    (hC (a,b)).hasFDerivAt.mul_const _
  have hsum := HasFDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
    HasFDerivAt.fun_sum fun b (_ : b ∈ Finset.univ) => hd a b
  change (fderiv ℝ (fun y => ∑ a, ∑ b, C a b y * (p a * p b)) x) e = _
  rw [hsum.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type, C, e]

/-- The variable multiplication part of the same Weyl commutator gives
the negative base derivative of the actual ΓΓ Euler density phase. -/
theorem actualDensityVariableLeading_eq_negativeBaseSymbol {ι : Type*}
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (β : E → E → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β)) (i j : ι) (x ξ : E)
    (hC : ∀ d : J, DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x)
    (hc : ∀ d : J, (fun y => c i j d y) =ᶠ[𝓝 x]
      fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) :
    let t (y : E) (p : Covector) := β y (WithLp.toLp 2 p)
    let p := physicalRadianCovector ξ
    (∑ d : J, -((p d.1 : ℂ) * (p d.2 : ℂ)) *
      coefficientCommutatorLeading (normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) (c i j d) x ξ) =
      -((∑ k, basePartial k (fun y q => frozenDensityPrincipalPhase S (G y) q i j) x p *
          momentumPartial k t x p : ℝ) : ℂ) := by
  intro t p
  rw [actualDensityVariableLeading_eq_negativeCoordinateContraction S G c β hβ i j x ξ hC hc]
  apply congrArg (fun r : ℝ => -(r : ℂ))
  simp only [actualDensityPhase_basePartial S G i j _ x p hC, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end Burnett.V03.Palatini
