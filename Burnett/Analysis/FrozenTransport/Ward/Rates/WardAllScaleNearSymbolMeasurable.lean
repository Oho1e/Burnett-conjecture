import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualGradient
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearVertexSmooth
import Burnett.Analysis.AngularCaps.ComparableTriadAngle
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxRecDepth 7900
set_option maxHeartbeats 12900000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.V08 (signedCyclicPhase)
open Burnett.A05 (endpointDirection)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise RealInnerProductSpace

open private directionDerivativeCoefficient from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

private theorem wardPurePhysicalNearWeight_measurable (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (κ δ : ℝ) :
    Measurable (wardPurePhysicalNearWeight ϑ κ δ) := by
  let p (x : Joint) := x.1
  let q (x : Joint) := x.2
  let r (x : Joint) := -(x.1+x.2)
  have cp : Continuous p := continuous_fst
  have cq : Continuous q := continuous_snd
  have cr : Continuous r := (continuous_fst.add continuous_snd).neg
  have low (u v w : Joint → E) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
      Measurable (fun x => lowSlotWeight ϑ κ (u x) (v x) (w x)) := by
    unfold lowSlotWeight
    exact hϑ.comp ((hu.norm.pow 2).measurable.div
      (continuous_const.mul ((hv.norm.pow 2).add (hw.norm.pow 2))).measurable)
  have wedge (u v : Joint → E) (hu : Continuous u) (hv : Continuous v) :
      Measurable (fun x => projectiveWedgeSq (u x) (v x)) := by
    have hGram : Continuous (fun x => coordinateWedgeSq (u x) (v x)) := by
      simpa only [coordinateWedgeSq_eq_gram] using
        (((hu.norm.pow 2).mul (hv.norm.pow 2)).sub ((hu.inner hv).pow 2))
    exact hGram.measurable.div ((hu.norm.pow 2).mul (hv.norm.pow 2)).measurable
  have angular (u v w : Joint → E) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
      Measurable (fun x => angularNearWeight ϑ δ (u x) (v x) (w x)) :=
    (hϑ.comp ((wedge u v hu hv).div measurable_const)).mul
      (hϑ.comp ((wedge u w hu hw).div measurable_const))
  have L₀ := low p q r cp cq cr
  have L₁ := low q r p cq cr cp
  have L₂ := low r p q cr cp cq
  have C := (((measurable_const (a := (1:ℝ))).sub L₀).sub L₁).sub L₂
  exact (((C.add (L₀.mul (angular p q r cp cq cr))).add (L₁.mul (angular q r p cq cr cp))).add
    (L₂.mul (angular r p q cr cp cq)))

private theorem wardNearGradientDirection_measurable (k : Index) :
    Measurable (wardNearGradientDirection k) := by
  unfold wardNearGradientDirection directionDerivativeCoefficient endpointDirection
  have h : Measurable (fun ξ : E => ‖ξ‖⁻¹ • ξ) := measurable_norm.inv.smul measurable_id
  exact measurable_const.mul
    (Complex.continuous_ofReal.measurable.comp (((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable).comp h))

/-- The actual normalizing denominator vanishes on the three coordinate
singular sets. On their open complement the original screen and vertex
give the ordinary measurable coefficient. -/
theorem wardNearGradientSymbol_measurable (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ)
    (κ δ wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (j : WardNearEntries) :
    Measurable (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j) := by
  classical
  let p (x : Joint) := x.1
  let q (x : Joint) := x.2
  let r (x : Joint) := -(x.1+x.2)
  let U : Set Joint := {x | p x ≠ 0 ∧ q x ≠ 0 ∧ r x ≠ 0}
  have dp : ContDiff ℝ ∞ p := contDiff_fst
  have dq : ContDiff ℝ ∞ q := contDiff_snd
  have dr : ContDiff ℝ ∞ r := (contDiff_fst.add contDiff_snd).neg
  have hU : IsOpen U := (isOpen_ne_fun dp.continuous continuous_const).inter
    ((isOpen_ne_fun dq.continuous continuous_const).inter (isOpen_ne_fun dr.continuous continuous_const))
  let C := wardNearCyclicColumn G a wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1
  let S := thinScreenAngular (inverseMatrix G) wi wo hm hη i o
  let T := wardNearScreenColumn G wi wo hm hη i o
  have hS (v : Joint → E) (hv : ContDiff ℝ ∞ v) (hne : ∀ x ∈ U, v x ≠ 0)
      (k l : OrderedPair) : ContDiffOn ℝ ∞ (fun x => T k (v x) l.1 l.2) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((S.smooth l k).comp hv.contDiffOn (fun x hx => hne x hx))
  have hV := wardComplexPrincipalVertex_contDiffOn U (fun _ => G) contDiffOn_const (fun _ _ => hG)
    p q r dp.contDiffOn dq.contDiffOn dr.contDiffOn
    (fun x => T j.1.1 (p x)) (fun x => T j.2.1.1 (q x)) (fun x => T j.2.2.1 (r x))
    (hS p dp (fun _ hx => hx.1) j.1.1) (hS q dq (fun _ hx => hx.2.1) j.2.1.1)
    (hS r dr (fun _ hx => hx.2.2) j.2.2.1)
  have hTest : ContDiffOn ℝ ∞ (fun x : Joint => signedCyclicPhase a (p x) (q x)) U :=
    ((ha.comp dp.contDiffOn (fun _ hx => hx.1)).add (ha.comp dq.contDiffOn (fun _ hx => hx.2.1))).add
      (ha.comp dr.contDiffOn (fun _ hx => hx.2.2))
  have hC : ContDiffOn ℝ ∞ C U := (Complex.ofRealCLM.contDiff.comp_contDiffOn hTest).mul hV
  let C' := U.piecewise C (fun _ => 0)
  have hC' : Measurable C' :=
    hC.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hW : Measurable (fun x => (wardPurePhysicalNearWeight ϑ κ δ x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (wardPurePhysicalNearWeight_measurable ϑ hϑ κ δ)
  have hD : Measurable (fun x => ((‖p x‖*‖q x‖*‖r x‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((dp.continuous.norm.mul dq.continuous.norm).mul dr.continuous.norm).measurable
  have hDirections := (((wardNearGradientDirection_measurable j.1.2).comp dp.continuous.measurable).mul
    ((wardNearGradientDirection_measurable j.2.1.2).comp dq.continuous.measurable)).mul
      ((wardNearGradientDirection_measurable j.2.2.2).comp dr.continuous.measurable)
  have hAll := (((measurable_const (a := (-Complex.I/3))).mul hW).mul (hC'.div hD)).mul hDirections
  let F (x : Joint) := (-Complex.I/3) * (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
    (C' x / ((‖p x‖*‖q x‖*‖r x‖ : ℝ) : ℂ)) *
    (wardNearGradientDirection j.1.2 (p x) * wardNearGradientDirection j.2.1.2 (q x) *
      wardNearGradientDirection j.2.2.2 (r x))
  have hF : Measurable F := hAll
  suffices F = wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j from this ▸ hF
  funext x
  by_cases hx : x ∈ U
  · dsimp only [F]
    rw [show C' x = C x from piecewise_eq_of_mem _ _ _ hx]
    rfl
  · have hZero : ‖p x‖*‖q x‖*‖r x‖ = 0 := by
      by_contra hn
      obtain ⟨⟨hp,hq⟩,hr⟩ := mul_ne_zero_iff.mp hn |>.imp_left mul_ne_zero_iff.mp
      exact hx ⟨norm_ne_zero_iff.mp hp,norm_ne_zero_iff.mp hq,norm_ne_zero_iff.mp hr⟩
    change _ * (C' x / ((‖p x‖*‖q x‖*‖r x‖ : ℝ) : ℂ)) * _ =
      _ * (C x / ((‖p x‖*‖q x‖*‖r x‖ : ℝ) : ℂ)) * _
    simp only [hZero,Complex.ofReal_zero,div_zero,mul_zero,zero_mul]

end Burnett.C02
