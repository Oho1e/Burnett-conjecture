import Burnett.Analysis.AllScaleTransfer.WeightedIntegerRadialFactor
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange

set_option autoImplicit false
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.A05

open Set Filter MeasureTheory
open Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open scoped Topology

private theorem symmetric_radial_triad_ne_zero_ae :
    ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ -(p.1+p.2) ≠ 0 := by
  have h (a : E) : ∀ᵐ x ∂(volume : Measure E), x ≠ a := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton a).ae_notMem (volume : Measure E)
  have u₁ : IsOpen {p : Joint | p.1 ≠ (0 : E)} := isOpen_ne_fun continuous_fst continuous_const
  have u₂ : IsOpen {p : Joint | p.2 ≠ (0 : E)} := isOpen_ne_fun continuous_snd continuous_const
  have u₃ : IsOpen {p : Joint | -(p.1+p.2) ≠ (0 : E)} :=
    isOpen_ne_fun (continuous_fst.add continuous_snd).neg continuous_const
  rw [Measure.volume_eq_prod E E]
  apply (Measure.ae_prod_iff_ae_ae (u₁.inter (u₂.inter u₃)).measurableSet).2
  filter_upwards [h 0] with x hx
  filter_upwards [h 0,h (-x)] with y hy hyx
  refine ⟨hx,hy,?_⟩
  intro hz
  have hxy : x+y = 0 := neg_eq_zero.mp hz
  exact hyx (by calc
    y = x+y-x := by abel
    _ = -x := by rw [hxy,zero_sub])

/-- Applying the same symmetric integer radial selection with unit weights to
all three actual Schwartz factors converges in the original Fourier integral. -/
theorem radianTrilinearForm_tendsto_symmetric_radial_truncations
    (m : Joint → ℂ) (f g h : SchwartzMap E ℂ)
    (hInt : Integrable (radianTrilinearWeight m f g h)) :
    let J (N : ℕ) := Finset.Icc (-(N : ℤ)) (N : ℤ)
    let cut (N : ℕ) (v : SchwartzMap E ℂ) := finiteIntegerRadialTruncation (J N) (fun _ => 1) v
    Tendsto (fun N : ℕ => radianTrilinearForm m (cut N f) (cut N g) (cut N h)) atTop
      (𝓝 (radianTrilinearForm m f g h)) := by
  classical
  intro J cut
  let W (N : ℕ) (x : E) : ℂ := (∑ j ∈ J N, integerRadialWindow j x : ℝ)
  let K := radianTrilinearWeight m f g h
  let P (N : ℕ) (p : Joint) : ℂ := W N p.1 * W N p.2 * W N (-(p.1+p.2))
  have spectrum (N : ℕ) (v : SchwartzMap E ℂ) (x : E) :
      radianFourier (cut N v : E → ℂ) x = W N x * radianFourier (v : E → ℂ) x := by
    simpa only [cut, W, one_mul, ← Complex.ofReal_sum] using
      finiteIntegerRadialTruncation_radianFourier (J N) (fun _ => 1) v x
  have weight (N : ℕ) : radianTrilinearWeight m (cut N f) (cut N g) (cut N h) =
      fun p => P N p * K p := by
    funext p
    simp only [P,K,radianTrilinearWeight,radianWeight,spectrum]
    ring
  have low : ∀ r : ℝ, Continuous (radialLowCutoff r) := by
    intro r
    unfold radialLowCutoff
    exact radialBallBump.continuous.comp (continuous_const.smul continuous_id)
  have expression (N : ℕ) (x : E) : W N x =
      (radialLowCutoff ((2 : ℝ)^N) x - radialLowCutoff (((2 : ℝ)^(N+1))⁻¹) x : ℝ) :=
    congrArg Complex.ofReal (integerRadialWindow_symmetric_sum N x)
  have continuousW (N : ℕ) : Continuous (W N) := by
    rw [funext (expression N)]
    exact Complex.continuous_ofReal.comp ((low _).sub (low _))
  have continuousP (N : ℕ) : Continuous (P N) :=
    (((continuousW N).comp continuous_fst).mul ((continuousW N).comp continuous_snd)).mul
      ((continuousW N).comp ((continuous_fst.add continuous_snd).neg))
  have lowRange (r : ℝ) (x : E) : 0 ≤ radialLowCutoff r x ∧ radialLowCutoff r x ≤ 1 :=
    ⟨radialBallBump.nonneg,radialBallBump.le_one⟩
  have normW (N : ℕ) (x : E) : ‖W N x‖ ≤ 1 := by
    rw [expression,Complex.norm_real,Real.norm_eq_abs,abs_le]
    have hA := lowRange ((2 : ℝ)^N) x
    have hB := lowRange (((2 : ℝ)^(N+1))⁻¹) x
    exact ⟨by linarith [hA.1,hB.2],by linarith [hA.2,hB.1]⟩
  have normP (N : ℕ) (p : Joint) : ‖P N p‖ ≤ 1 := by
    simp only [P,norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (normW N p.1) (norm_nonneg _) (normW N p.2))
      (norm_nonneg _) (normW N (-(p.1+p.2)))
  have unit (x : E) (hx : x ≠ 0) : ∀ᶠ N : ℕ in atTop, W N x = 1 := by
    filter_upwards [integerRadialWindow_eventually_symmetric x] with N hN
    simpa only [W,J,if_neg hx,Complex.ofReal_one] using congrArg Complex.ofReal hN.2
  have hK : Integrable K := hInt
  have lim : Tendsto (fun N : ℕ => ∫ p, P N p * K p) atTop (𝓝 (∫ p, K p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖K p‖)
    · exact Eventually.of_forall (fun N => (continuousP N).aestronglyMeasurable.mul hK.1)
    · exact Eventually.of_forall (fun N => Eventually.of_forall fun p => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg (K p)) (normP N p))
    · exact hK.norm
    · filter_upwards [symmetric_radial_triad_ne_zero_ae] with p hp
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [unit p.1 hp.1,unit p.2 hp.2.1,unit (-(p.1+p.2)) hp.2.2] with N hp hq hr
      simp only [P,hp,hq,hr,mul_one,one_mul]
  simpa only [radianTrilinearForm,weight,K] using lim.const_smul ((tau^8)⁻¹ : ℝ)

end Burnett.A05
