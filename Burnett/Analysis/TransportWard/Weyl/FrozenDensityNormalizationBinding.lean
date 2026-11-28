import Burnett.Analysis.TransportWard.Weyl.FrozenDensityPrincipalPhase
import Burnett.Analysis.TransportWard.Weyl.NormalizedHessianSymbol

/-! The phase of the frozen operator is the previously checked actual
coordinate Hessian in the orthonormal symmetric field slots. -/

set_option autoImplicit false

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol
open Burnett.V02
open Burnett.Analysis.TransportWardSymbol (Mat principalHessianPairing)

theorem frozenDensityPrincipalPhase_eq_densityEulerPrincipalMatrix
    {ι : Type*} (S : ι → Mat) (G : Mat) :
    frozenDensityPrincipalPhase S G = densityEulerPrincipalMatrix S G := rfl

theorem frozenDensityPrincipalPhase_orthonormal_eq_fourierHessian
    (G : Mat) (p : Covector) (i j : SymmetricMetricSlot) :
    frozenDensityPrincipalPhase orthonormalMetricDirection G p i j =
      principalHessianPairing G p (orthonormalMetricDirection j) (orthonormalMetricDirection i) :=
  densityEulerPrincipalMatrix_eq_fourierHessian orthonormalMetricDirection G p i j

end Burnett.V03.Palatini
