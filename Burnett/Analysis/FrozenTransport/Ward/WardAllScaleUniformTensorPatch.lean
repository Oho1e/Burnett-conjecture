import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorAssembly
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleRawTrilinear
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowLieTrilinear
import Mathlib.LinearAlgebra.Multilinear.Curry

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 22000000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.A05
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ContDiff Topology

open private wardMiddleTrilinear wardMiddleTrilinear_eq_symbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor

private def wardMiddleTensorTrilinear (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (x : Joint) : WardTensorTrilinear := by
  let one := (MultilinearMap.ofSubsingletonₗ ℂ ℂ ComplexComponents ℂ (0 : Fin 1)).toLinearMap
  let two : (ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ℂ) →ₗ[ℂ]
      MultilinearMap ℂ (fun _ : Fin 2 => ComplexComponents) ℂ :=
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 2 => ComplexComponents) ℂ).symm.toLinearMap.comp
      (LinearMap.llcomp ℂ ComplexComponents (ComplexComponents →ₗ[ℂ] ℂ) _ one)
  exact (two.comp (wardMiddleTrilinear ϑ κ m w a x)).uncurryLeft

private theorem wardMiddleTensorTrilinear_apply (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (x : Joint) (H : Fin 3 → ComplexComponents) :
    wardMiddleTensorTrilinear ϑ κ m w a x H = wardLowGaugeMiddleSymbol ϑ κ m w a (H 0) (H 1) (H 2) x :=
  wardMiddleTrilinear_eq_symbol ϑ κ m w a x (H 0) (H 1) (H 2)

/-- Physical slots for the seven terms carrying a physical phase on the
first-low and comparable sectors of the original Ward formula. -/
def wardPhysicalPhaseSlots : Fin 7 → Fin 3 → Bool :=
  ![![false,true,true], ![false,true,true], ![true,true,false], ![true,false,false], ![false,true,false],
    ![true,true,false], ![true,false,false]]

def wardPhysicalPhaseTensorSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ) :
    Fin 7 → Joint → WardTensorTrilinear :=
  ![wardMiddleTensorTrilinear ϑ κ m w a,
    wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a),
    wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a),
    wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a),
    wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear m w a),
    wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a),
    wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a)]

end Burnett.C02
