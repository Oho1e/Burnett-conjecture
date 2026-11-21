import Burnett.Analysis.PrincipalEnergy.Commutator.PackingSquare
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 4)

def compactWaveletKernel (ψ : SchwartzMap Space ℂ) (s : ℝ) (z : Space) : ℂ :=
  (s^4)⁻¹ • ψ (s⁻¹ • z)

def compactWaveletAction (ψ : SchwartzMap Space ℂ) (s : ℝ) (f : Space → ℂ) (x : Space) : ℂ :=
  ∫ y, compactWaveletKernel ψ s (x-y) * f y

private theorem compactWaveletKernel_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    Integrable (compactWaveletKernel ψ s) := (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _

private theorem compactWaveletKernel_translate (K : Space → ℂ) (hK : Integrable K) (x : Space) :
    Integrable (fun y => K (x-y)) ∧ (∫ y, K (x-y)) = ∫ y, K y := by
  have hT := (volume : Measure Space).measurePreserving_sub_left x
  refine ⟨hT.integrable_comp_of_integrable hK,?_⟩
  rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hK.aestronglyMeasurable),hT.map_eq]

/-- The exact four-dimensional scaled wavelet preserves its total integral. -/
theorem compactWaveletKernel_integral_eq (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    (∫ z, compactWaveletKernel ψ s z) = ∫ z, ψ z := by
  unfold compactWaveletKernel
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume _ hs.le,
    finrank_euclideanSpace_fin, smul_smul, inv_mul_cancel₀ (pow_ne_zero 4 hs.ne'),one_smul]

private theorem compactWaveletKernel_pair_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ)
    (hs : 0<s) (b : Space → ℂ) (hb : MemLp b 2 volume) (x : Space) :
    Integrable (fun y => compactWaveletKernel ψ s (x-y)*b y) := by
  let K (y : Space) := compactWaveletKernel ψ s (x-y)
  let D := |(s^4)⁻¹| *SchwartzMap.seminorm ℝ 0 0 ψ
  have hKi : Integrable K :=
    (compactWaveletKernel_translate _ (compactWaveletKernel_integrable ψ s hs) x).1
  have hD : 0 ≤ D := mul_nonneg (abs_nonneg _) (apply_nonneg _ _)
  have hBound (y : Space) : ‖K y‖ ≤ D := by
    change ‖(s^4)⁻¹ • ψ (s⁻¹ • (x-y))‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ ψ _) (abs_nonneg _)
  have hSq : Integrable (fun y => ‖b y‖^2) (volume : Measure Space) :=
    hb.integrable_norm_pow (p := 2) (by decide)
  refine (hKi.norm.add (hSq.const_mul D)).mono'
    (hKi.aestronglyMeasurable.mul hb.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  change ‖K y*b y‖ ≤ ‖K y‖ + D*‖b y‖^2
  rw [norm_mul]
  by_cases h : ‖b y‖ ≤ 1
  · exact (mul_le_of_le_one_right (norm_nonneg _) h).trans
      (le_add_of_nonneg_right (mul_nonneg hD (sq_nonneg _)))
  · have hbb : ‖b y‖ ≤ ‖b y‖^2 := by
      simpa only [one_mul,pow_two] using mul_le_mul_of_nonneg_right (le_of_not_ge h) (norm_nonneg (b y))
    exact (mul_le_mul (hBound y) hbb (norm_nonneg _) hD).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- The actual compact wavelet annihilates the subtracted constant and uses
only the enlarged ball in each of the stated local convolution values. -/
theorem compactWaveletAction_localize (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0)
    (b : Space → ℂ) (hb : MemLp b 2 volume) (m : ℂ) (c x : Space) (R s : ℝ)
    (hs : 0<s) (hSR : s≤R) (hx : x∈ball c R) :
    compactWaveletAction ψ s b x =
      compactWaveletAction ψ s ((ball c (2*R)).indicator (fun y => b y-m)) x := by
  let K := compactWaveletKernel ψ s
  have hKi : Integrable K := compactWaveletKernel_integrable ψ s hs
  have hKt := compactWaveletKernel_translate K hKi x
  have h0 : (∫ y, K (x-y)) = 0 := hKt.2.trans ((compactWaveletKernel_integral_eq ψ s hs).trans hMean)
  have hB := compactWaveletKernel_pair_integrable ψ s hs b hb x
  have hConst : Integrable (fun y => K (x-y)*m) := hKt.1.mul_const m
  have hSub (y : Space) : K (x-y)*b y - K (x-y)*m =
      K (x-y)*(ball c (2*R)).indicator (fun y => b y-m) y := by
    by_cases hy : y ∈ ball c (2*R)
    · rw [indicator_of_mem hy,mul_sub]
    have hxc : ‖x-c‖ < R := by simpa [mem_ball,dist_eq_norm] using hx
    have hyc : 2*R ≤ ‖y-c‖ := by simpa [mem_ball,dist_eq_norm,not_lt] using hy
    have htri : ‖y-c‖ ≤ ‖x-y‖+‖x-c‖ := by
      have hh := norm_add_le (y-x) (x-c)
      rw [show y-x + (x-c) = y-c by abel] at hh
      simpa only [norm_sub_rev y x] using hh
    have hSmall : s < ‖x-y‖ := by linarith
    have hZ : 1 < ‖s⁻¹ • (x-y)‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),← div_eq_inv_mul]
      exact (one_lt_div₀ hs).mpr hSmall
    have hZero : K (x-y) = 0 := by
      dsimp only [K,compactWaveletKernel]
      rw [hψ _ hZ,smul_zero]
    simp [hZero]
  change (∫ y, K (x-y)*b y) = ∫ y, K (x-y)*(ball c (2*R)).indicator (fun y => b y-m) y
  simp only [← hSub]
  rw [integral_sub hB hConst,integral_mul_const,h0,zero_mul,sub_zero]

end Burnett.Analysis.CarlesonEmbedding
