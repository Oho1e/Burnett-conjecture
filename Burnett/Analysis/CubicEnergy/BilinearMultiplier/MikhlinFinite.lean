import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open Finset MeasureTheory Filter Burnett.Fourier
open scoped Topology ENNReal

private theorem zero_modulation (a : SchwartzMap E ℂ) (ξ : E) :
    modulatedWindowSymbol a 0 ξ = a ξ := by
  change Complex.exp ((↑(2*Real.pi*inner ℝ ξ 0):ℂ)*Complex.I) * a ξ = a ξ
  simp

def mikhlinBands (a : SchwartzMap E ℂ)
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t) (I : Finset ℕ) :
    BoundedSymbol E :=
  signedBandsSymbol (modulatedWindowSymbol a 0) (fun ξ h => cut ξ (by simpa only [zero_modulation] using h))
    t ht (fun _ => 1) (by simp) I

theorem mikhlinBands_eval (a : SchwartzMap E ℂ)
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t) (I : Finset ℕ) (ξ : E) :
    mikhlinBands a cut t ht I ξ = ∑ k ∈ I, a (((2:ℝ)^k*t) • ξ) := by
  simp [mikhlinBands,signedBandsSymbol,zero_modulation]

private theorem sum_ae (A : ℕ → ComplexL2 E) (I : Finset ℕ) :
    (fun x => (∑ k ∈ I, A k) x) =ᵐ[volume] fun x => ∑ k ∈ I, A k x := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [sum_empty] using Lp.coeFn_zero ℂ 2 (volume : Measure E)
  | @insert k I hk ih =>
    simp only [sum_insert hk]
    filter_upwards [Lp.coeFn_add (A k) (∑ j ∈ I, A j),ih] with x h h'
    simp only [h,Pi.add_apply,h']

theorem mikhlinBands_test (a : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t) (I : Finset ℕ)
    (f : SchwartzMap E ℂ) :
    (fourierMultiplier (mikhlinBands a cut t ht I) (f.toLp 2 volume) : E → ℂ) =ᵐ[volume]
      kernelApply (finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t 0 I (fun _ => 1)) f := by
  let F := f.toLp 2 volume
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let s := fun k : ℕ => (2:ℝ)^k*t
  have sp (k : ℕ) : 0 < s k := mul_pos (by positivity) ht
  let B := fun k => rescaleSymbol (modulatedWindowSymbol a 0) (s k) (sp k)
  let M := mikhlinBands a cut t ht I
  let K := fun k => shiftedSpatialKernel φ (s k) 0
  have eq : fourierMultiplier M F = ∑ k ∈ I, fourierMultiplier (B k) F := by
    apply fourierL2Equiv.injective
    simp only [map_sum, fourier_fourierMultiplier]
    apply Lp.ext
    let v := fourierL2Equiv F
    have he : ∀ᵐ ξ ∂volume, ∀ k : ℕ, symbolL2 (B k) v ξ = B k ξ * v ξ := ae_all_iff.mpr (fun k => symbolL2_ae (B k) v)
    filter_upwards [symbolL2_ae M v,sum_ae (fun k => symbolL2 (B k) v) I,he] with ξ h₁ h₂ h₃
    change symbolL2 M v ξ = (∑ k ∈ I, symbolL2 (B k) v) ξ
    rw [h₁,h₂,mikhlinBands_eval,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [h₃ k]
    simp only [B,rescaleSymbol,zero_modulation,s]
  have aeK : ∀ᵐ x ∂volume, ∀ k : ℕ, fourierMultiplier (B k) F x = kernelApply (K k) f x := by
    apply ae_all_iff.mpr
    intro k
    exact (shiftedWindow_L2_ae a ha f (s k) (sp k) 0).trans (Eventually.of_forall fun x =>
      shifted_window_physical a f (s k) (sp k) 0 x)
  have intgr (k : ℕ) (x : E) : Integrable (fun y : E => K k (x-y) * f y) := by
    obtain ⟨hK,hi,_,D,hD⟩ := finite_kernel_regular φ t ht 0 {k} (fun _ => 1)
    have eq : finiteWindowKernel φ t 0 {k} (fun _ => 1) = K k := by
      funext z
      simp [finiteWindowKernel,K,s]
    rw [eq] at hK hi hD
    exact kernel_integrand_Lp (K k) hK hi D hD 2 (by norm_num) f (by simpa using f.memLp 2 volume) x
  change (fourierMultiplier M F : E → ℂ) =ᵐ[volume] _
  rw [eq]
  filter_upwards [sum_ae (fun k => fourierMultiplier (B k) F) I,aeK] with x hsum hk
  rw [hsum]
  simp only [hk,kernelApply]
  rw [← integral_finset_sum I (fun k _ => intgr k x)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [finiteWindowKernel,one_mul,sum_mul]
  rfl

/-- The genuine finite L² Fourier multiplier is the same physical convolution
on every L² input, even without an L¹ Fourier transform. -/
theorem mikhlinBands_all_L2 (a : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t) (I : Finset ℕ)
    (f : E → ℂ) (hf : MemLp f 2 volume) :
    (fourierMultiplier (mikhlinBands a cut t ht I) (hf.toLp f) : E → ℂ) =ᵐ[volume]
      kernelApply (finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t 0 I (fun _ => 1)) f := by
  let A := fourierMultiplier (mikhlinBands a cut t ht I)
  let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t 0 I (fun _ => 1)
  obtain ⟨_,_,h₂,_,_⟩ := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) t ht 0 I (fun _ => 1)
  obtain ⟨v,hv,conv⟩ := mem_closure_iff_seq_limit.mp (schwartz_toLp_denseRange (hf.toLp f))
  choose g hg using hv
  have eq (n : ℕ) : (g n).toLp 2 volume = v n := hg n
  have cv : Tendsto (fun n => A (v n)) atTop (𝓝 (A (hf.toLp f))) := A.continuous.continuousAt.tendsto.comp conv
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp cv).exists_seq_tendsto_ae
  have tests : ∀ᵐ x ∂volume, ∀ n : ℕ, A (v n) x = kernelApply K (g n) x := by
    apply ae_all_iff.mpr
    intro n
    rw [← eq n]
    exact mikhlinBands_test a ha cut t ht I (g n)
  filter_upwards [hae,tests] with x h₁ h₂'
  obtain ⟨k,hk⟩ := kernelApply_as_inner K h₂ x
  have h' (n : ℕ) : A (v n) x = inner ℂ k (v n) := by
    rw [h₂' n, ← eq n]
    exact hk _ ((g n).memLp 2 volume)
  have hz : Tendsto (fun i => A (v (ns i)) x) atTop (𝓝 (kernelApply K f x)) := by
    simp_rw [h',hk f hf]
    exact tendsto_const_nhds.inner (conv.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique h₁ hz

end Burnett.A02.FrequencySplit
