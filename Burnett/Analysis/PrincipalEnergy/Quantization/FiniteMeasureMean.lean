import Burnett.Analysis.PrincipalEnergy.Quantization.CommutatorT1Oscillation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Set Filter Burnett.Microlocal.AngularDyadicKernel
open scoped ComplexConjugate

def finiteMeasureMean (μ : Measure E) (F : E → ℂ) : ℂ :=
  (μ.real univ)⁻¹ • ∫ x, F x ∂μ

private theorem norm_add_sq_complex (u v : ℂ) :
    ‖u+v‖^2 = ‖u‖^2+2*(conj u*v).re+‖v‖^2 := by
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- The actual complex mean minimizes the square oscillation over a finite
measure and gives the exact excess for every other center. -/
theorem squareOscillation_eq_mean_add_constant (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : 0 < μ.real univ) (F : E → ℂ) (hF : MemLp F 2 μ) (b : ℂ) :
    (∫ x, ‖F x-b‖^2 ∂μ) =
      (∫ x, ‖F x-finiteMeasureMean μ F‖^2 ∂μ) + μ.real univ * ‖finiteMeasureMean μ F-b‖^2 := by
  let m := finiteMeasureMean μ F
  let G (x : E) := F x-m
  let c := m-b
  have hFi : Integrable F μ := hF.integrable (by norm_num)
  have hGi : Integrable G μ := hFi.sub (integrable_const _)
  have hZero : (∫ x, G x ∂μ) = 0 := by
    change (∫ x, F x-m ∂μ) = 0
    rw [integral_sub hFi (integrable_const _),integral_const]
    change (∫ x, F x ∂μ) - μ.real univ • ((μ.real univ)⁻¹ • ∫ x, F x ∂μ) = 0
    rw [smul_smul,mul_inv_cancel₀ hμ.ne',one_smul,sub_self]
  have hGC : Integrable (fun x => conj (G x)) μ := hGi.norm.mono'
    hGi.aestronglyMeasurable.star (Eventually.of_forall fun x => (Complex.norm_conj (G x)).le)
  have hCross : Integrable (fun x => conj (G x)*c) μ := hGC.mul_const c
  have hRe : Integrable (fun x => (conj (G x)*c).re) μ := hCross.re
  have hReZero : (∫ x, (conj (G x)*c).re ∂μ) = 0 := by
    change (∫ x, RCLike.re (conj (G x)*c) ∂μ) = 0
    simp only [integral_re hCross,integral_mul_const,integral_conj,hZero,map_zero,zero_mul]
  have hG : MemLp G 2 μ := hF.sub (memLp_const _)
  have hGSq : Integrable (fun x => ‖G x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hSum (x : E) : F x-b = G x+c := by dsimp [G,c]; ring
  have hForm (x : E) : ‖F x-b‖^2 = ‖G x‖^2+2*(conj (G x)*c).re+‖c‖^2 := by
    rw [hSum,norm_add_sq_complex]
  simp_rw [hForm]
  have hRe2 : Integrable (fun x => 2*(conj (G x)*c).re) μ := hRe.const_mul 2
  have hS : Integrable (fun x => ‖G x‖^2+2*(conj (G x)*c).re) μ := hGSq.add hRe2
  have hC : Integrable (fun _ : E => ‖c‖^2) μ := integrable_const _
  rw [integral_add hS hC,integral_add hGSq hRe2,integral_const_mul,hReZero,mul_zero,add_zero,integral_const,smul_eq_mul]

end Burnett.Analysis.FirstOrderDyadic
