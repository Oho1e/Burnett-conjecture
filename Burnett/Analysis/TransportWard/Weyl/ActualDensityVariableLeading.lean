import Burnett.Analysis.TransportWard.Weyl.RealWeylCoefficientLeading
import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient

/-! Read back the actual variable principal density coefficients in the
negative frequency contraction, before summing the full bracket. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4100

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.RotatingNullMoments.CanonicalHamilton (momentumPartial)
open scoped BigOperators ContDiff Topology

local notation "J" => Fin 4 × Fin 4

theorem actualDensityVariableLeading_eq_negativeCoordinateContraction {ι : Type*}
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (β : E → E → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β)) (i j : ι) (x ξ : E)
    (hC : ∀ d : J, DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x)
    (hc : ∀ d : J, (fun y => c i j d y) =ᶠ[𝓝 x]
      fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) :
    let t (y : E) (p : Covector) := β y (WithLp.toLp 2 p)
    let p := physicalRadianCovector ξ
    (∑ d : J, -((p d.1 : ℂ) * (p d.2 : ℂ)) *
      coefficientCommutatorLeading (normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) (c i j d) x ξ) =
      -((∑ d : J, (p d.1 * p d.2) * ∑ k,
        fderiv ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x (coordinateDirection k) *
          momentumPartial k t x p : ℝ) : ℂ) := by
  intro t p
  have hDer (d : J) (k : Fin 4) :
      (frozenSchwartzCoordinatePartial k (c i j d)) x =
        (fderiv ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x (coordinateDirection k) : ℂ) := by
    let f (y : E) := metricActionCoefficient S (d.1,i) (d.2,j) (G y)
    have hd : fderiv ℝ (fun y => (f y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) :=
      (Complex.ofRealCLM.hasFDerivAt.comp x (hC d).hasFDerivAt).fderiv
    change (fderiv ℝ (fun y => c i j d y) x) (coordinateDirection k) = _
    have hGerm : (fun y => c i j d y) =ᶠ[𝓝 x] (fun y => (f y : ℂ)) := hc d
    rw [hGerm.fderiv_eq,hd,ContinuousLinearMap.comp_apply]
    rfl
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [coefficientCommutatorLeading_normalizedWeyl β hβ]
  simp only [hDer,t]
  ring

end Burnett.V03.Palatini
