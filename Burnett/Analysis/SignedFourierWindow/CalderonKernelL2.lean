import Burnett.Analysis.SignedFourierWindow.CalderonCancellation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Burnett.Fourier Filter Topology ComplexConjugate
open scoped ENNReal

/-- A fixed translated convolution value is a continuous linear functional on L². -/
theorem kernelApply_as_inner (K : Space → ℂ) (hk : MemLp K 2 volume) (x : Space) :
    ∃ k : ComplexL2 Space, ∀ (f : Space → ℂ) (hf : MemLp f 2 volume),
      kernelApply K f x = inner ℂ k (hf.toLp f) := by
  let b := fun y : Space => conj (K (x-y))
  have hb : MemLp b 2 volume := (hk.comp_measurePreserving (volume.measurePreserving_sub_left x)).star
  refine ⟨hb.toLp b,?_⟩
  intro f hf
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp,hf.coeFn_toLp] with y h₁ h₂
  simp [h₁,h₂,b,mul_comm]

/-- Extend the given Schwartz bound to every L² input for the same physical
convolution kernel, by pointwise continuity against translated L² columns and Fatou. -/
theorem kernelApply_L2_extension (K : Space → ℂ) (hk : MemLp K 2 volume)
    (B : ℝ) (hB : 0 ≤ B) (test : ∀ f : SchwartzMap Space ℂ, ∃ u : ComplexL2 Space,
      (u : Space → ℂ) =ᵐ[volume] kernelApply K f ∧ ‖u‖ ≤ B*‖f.toLp 2 volume‖)
    (f : Space → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm (kernelApply K f) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by
  classical
  obtain ⟨v,hv,conv⟩ := mem_closure_iff_seq_limit.mp (schwartz_toLp_denseRange (hf.toLp f))
  choose s hs using hv
  have eq (n : ℕ) : (s n).toLp 2 volume = v n := hs n
  choose u hu bound using fun n => test (s n)
  have point (x : Space) : Tendsto (fun n => kernelApply K (s n) x) atTop (𝓝 (kernelApply K f x)) := by
    obtain ⟨k,hk'⟩ := kernelApply_as_inner K hk x
    have re (n : ℕ) : kernelApply K (s n) x = inner ℂ k (v n) := by
      rw [← eq n]
      exact hk' _ ((s n).memLp 2 volume)
    simp_rw [re,hk' f hf]
    exact tendsto_const_nhds.inner conv
  have fatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := (volume : Measure Space))
    (fun n => (Lp.aestronglyMeasurable (u n)).congr (hu n)) _ (Eventually.of_forall point)
  have major (n : ℕ) : eLpNorm (kernelApply K (s n)) 2 volume ≤ ENNReal.ofReal (B*‖v n‖) := by
    rw [← eLpNorm_congr_ae (hu n),← Lp.enorm_def,← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal ((bound n).trans_eq (by rw [eq n]))
  refine fatou.trans ((Filter.liminf_le_liminf (Eventually.of_forall major)).trans_eq ?_)
  have lim : Tendsto (fun n => ENNReal.ofReal (B*‖v n‖)) atTop
        (𝓝 (ENNReal.ofReal (B*‖hf.toLp f‖))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul conv.norm)
  rw [lim.liminf_eq,ENNReal.ofReal_mul hB,ofReal_norm_eq_enorm,Lp.enorm_toLp]

end Burnett.Analysis.SignedFourierWindow
