import Burnett.Analysis.FrozenTransport.FrozenCubicOddTest
import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.V03.Palatini

open Function Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open scoped ComplexConjugate ContDiff

open private energyPartial_real from Burnett.Analysis.FrozenTransport.FrozenCubicOddTest

theorem energyPartial_re_eq_fderiv (f : SchwartzMap E ℂ) (a : Index) (x : E) :
    (energyPartial a f x).re = fderiv ℝ (fun y => (f y).re) x (coordinateBasis a) := by
  have hD := (Complex.reCLM.hasFDerivAt.comp x (f.differentiable x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y).re) x = Complex.reCLM.comp (fderiv ℝ (f : E → ℂ) x) at hD
  have hb : coordinateBasis a = EuclideanSpace.single a 1 := EuclideanSpace.basisFun_apply _ _ a
  simpa only [energyPartial, SchwartzMap.pderivCLM_apply, ← hb] using
    DFunLike.congr_fun hD.symm (coordinateBasis a)

theorem coe_re_eq_of_conj_eq (z : ℂ) (hz : conj z = z) : Complex.ofReal z.re = z := by
  apply Complex.ext
  · rfl
  · exact (Complex.conj_eq_iff_im.mp hz).symm

theorem realEnergyField_jets {J : Type} [Fintype J] (u : RealEnergyField J) :
    let h (x : E) (i : J) : ℝ := (u.val i x).re
    (∀ x s, Complex.ofReal (coordinateMetricFirstJet h x s) = energyPartial s.1 (u.val s.2) x) ∧
    (∀ x a s, Complex.ofReal (coordinateMetricSecondJet h x a s) =
      energyPartial a (energyPartial s.1 (u.val s.2)) x) := by
  intro h
  have hs : ContDiff ℝ ∞ h := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (u.val i).smooth'
  have hJet (x : E) (s : ActionSlot J) :
      coordinateMetricFirstJet h x s = (energyPartial s.1 (u.val s.2) x).re := by
    let P : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj s.2
    have hD := (P.hasFDerivAt.comp x (hs.differentiable (by simp) x).hasFDerivAt).fderiv
    rw [energyPartial_re_eq_fderiv]
    change (P.comp (fderiv ℝ h x)) (coordinateBasis s.1) = (fderiv ℝ (P ∘ h) x) (coordinateBasis s.1)
    rw [hD]
  refine ⟨fun x s => ?_, fun x a s => ?_⟩
  · rw [hJet]
    exact coe_re_eq_of_conj_eq _ (energyPartial_real _ (u.property s.2) s.1 x)
  · unfold coordinateMetricSecondJet
    rw [funext (fun y => hJet y s), ← energyPartial_re_eq_fderiv]
    exact coe_re_eq_of_conj_eq _ (energyPartial_real _ (energyPartial_real _ (u.property s.2) s.1) a x)

end Burnett.V03.Palatini
