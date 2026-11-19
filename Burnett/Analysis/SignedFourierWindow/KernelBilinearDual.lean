import Burnett.Analysis.SignedFourierWindow.KernelDualPairing
import Burnett.Analysis.SignedFourierWindow.KernelDualPower

set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Set MeasureTheory Filter
open scoped ENNReal

/-- The full bound on the reflected convolution at the conjugate exponent
implies the same bound on the original convolution above exponent two. -/
theorem kernelLp_of_reflected_conjugate (K : Space → ℂ) (hK : Continuous K) (hi : Integrable K)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (p : ℝ) (hp : 2<p) (B : ℝ≥0∞)
    (bound : ∀ h : Space → ℂ, MemLp h (ENNReal.ofReal (p/(p-1))) volume →
      eLpNorm (kernelApply (fun z => K (-z)) h) (ENNReal.ofReal (p/(p-1))) volume ≤
        B * eLpNorm h (ENNReal.ofReal (p/(p-1))) volume)
    (f : Space → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (kernelApply K f) (ENNReal.ofReal p) volume ≤ B * eLpNorm f (ENNReal.ofReal p) volume := by
  apply kernelLp_exhaustion K hK hi D hD p (by linarith) B _ f hf
  intro g mg ig
  let u := kernelApply K g
  let h := kernelDualPower p u
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (p/(p-1))
  let N := eLpNorm u P volume
  let R := kernelApply (fun z => K (-z)) h
  have hpm : 0<p-1 := by linarith
  have mu : Measurable u := measurable_kernelApply K g hK mg
  obtain ⟨iu,bu⟩ := kernelApply_L1_bounded K hi D hD g ig
  obtain ⟨mh,ih,pu,ph,eh,ep⟩ := kernelDualPower_norms p hp u mu iu _ bu
  have mR : Measurable R := measurable_kernelApply _ h (hK.comp continuous_neg) mh
  have holder : p.HolderConjugate (p/(p-1)) := Real.HolderConjugate.conjExponent (by linarith)
  letI : ENNReal.HolderConjugate P Q := holder.ennrealOfReal
  have pair : (∫ x, u x * h x) = ∫ y, g y * R y :=
    kernelApply_bilinear_reflection K hK D hD g h mg mh ig ih
  have mom : N^p ≤ (B * eLpNorm g P volume)*N^(p-1) := by
    calc
      _ = ‖∫ y, g y * R y‖ₑ := ep.symm.trans (congrArg (fun z : ℂ => ‖z‖ₑ) pair)
      _ ≤ ∫⁻ y, ‖g y * R y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (g • R) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm g P volume * eLpNorm R Q volume :=
        eLpNorm_smul_le_mul_eLpNorm mR.aestronglyMeasurable mg.aestronglyMeasurable
      _ ≤ eLpNorm g P volume * (B * eLpNorm h Q volume) := mul_le_mul_left' (bound h ph) _
      _ = _ := by rw [eh]; ring
  change N ≤ B * eLpNorm g P volume
  by_cases nz : N=0
  · rw [nz]
    exact zero_le _
  apply (ENNReal.mul_le_mul_right (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr nz) hpm.le).ne'
    (ENNReal.rpow_lt_top_of_nonneg hpm.le pu.2.ne).ne).mp
  have split : N * N^(p-1) = N^p := by
    have s := ENNReal.rpow_add_of_nonneg (x := N) 1 (p-1) (by norm_num) hpm.le
    rw [ENNReal.rpow_one,show 1+(p-1)=p by ring] at s
    exact s.symm
  exact split.le.trans mom
end Burnett.Analysis.SignedFourierWindow
