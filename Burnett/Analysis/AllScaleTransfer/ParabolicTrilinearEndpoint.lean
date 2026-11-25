import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Burnett.Analysis.AngularCaps.LinearLpPullback
import Burnett.Analysis.AngularCaps.CapFrequencyCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory
open Burnett.A02.FrequencySplit (Joint)
open Burnett.Analysis.ProjectiveNullCaps
open scoped ENNReal

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem toReal_oneThird_scale {r : ℝ} (hr : 0 ≤ r) :
    ((ENNReal.ofReal r)^((1 / (3 : ℝ≥0∞)).toReal)).toReal = r^(1/3 : ℝ) := by
  rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal hr,ENNReal.toReal_div,
    ENNReal.toReal_one,ENNReal.toReal_ofNat]

theorem inverseDual_linearLpPullback_L3_norm (A : Space ≃L[ℝ] Space) (f : ComplexLp 3) :
    ‖linearLpPullback (p := 3) (by norm_num) (physicalDualEquiv A).symm f‖ =
      (linearJacobian A)^(1/3 : ℝ) * ‖f‖ := by
  rw [linearLpPullback_norm,pullbackNormFactor,linearJacobian_symm,inv_inv,
    linearJacobian_physicalDualEquiv,toReal_oneThird_scale (linearJacobian_pos A).le]

/-- The same physical pullback maps a Bochner L³ field to a Bochner L³ field. -/
theorem memLp_inverseDual_L3 {V : Type*} [NormedAddCommGroup V] (A : Space ≃L[ℝ] Space)
    {f : Space → V} (hf : MemLp f 3 volume) :
    MemLp (f ∘ (physicalDualEquiv A).symm) 3 volume := by
  let D := (physicalDualEquiv A).symm
  have h : MemLp f 3 (Measure.map D volume) := by
    change MemLp f 3 (Measure.map (⇑D) volume)
    rw [map_linear_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map D.continuous.measurable.aemeasurable

theorem inverseDual_toLp_L3_norm {V : Type*} [NormedAddCommGroup V] (A : Space ≃L[ℝ] Space)
    {f : Space → V} (hf : MemLp f 3 volume) :
    ‖(memLp_inverseDual_L3 A hf).toLp (f ∘ (physicalDualEquiv A).symm)‖ =
      (linearJacobian A)^(1/3 : ℝ) * ‖hf.toLp f‖ := by
  let D := (physicalDualEquiv A).symm
  have map_eq : Measure.map D (volume : Measure Space) = ENNReal.ofReal (linearJacobian A) • volume := by
    change Measure.map (⇑D) (volume : Measure Space) = _
    rw [map_linear_volume,show linearJacobian D = (linearJacobian (physicalDualEquiv A))⁻¹ from
      linearJacobian_symm (physicalDualEquiv A),inv_inv,linearJacobian_physicalDualEquiv]
  have hmap : MemLp f 3 (Measure.map D volume) := by
    rw [map_eq]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  simp only [Lp.norm_toLp]
  change (eLpNorm (f ∘ D) 3 volume).toReal =
    (linearJacobian A)^(1/3 : ℝ) * (eLpNorm f 3 volume).toReal
  rw [← eLpNorm_map_measure hmap.aestronglyMeasurable D.continuous.measurable.aemeasurable,
    map_eq,eLpNorm_smul_measure_of_ne_top (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),smul_eq_mul,
    ENNReal.toReal_mul,toReal_oneThird_scale (linearJacobian_pos A).le]

private theorem cancel_three_L3_scales {J : ℝ} (hJ : 0 < J) (a b c : ℝ) :
    J⁻¹ * (J^(1/3 : ℝ)*a) * (J^(1/3 : ℝ)*b) * (J^(1/3 : ℝ)*c) = a*b*c := by
  have hc : (J^(1/3 : ℝ))^3 = J := by
    rw [← Real.rpow_mul_natCast hJ.le]
    norm_num
  calc
    _ = (J⁻¹ * (J^(1/3 : ℝ))^3) * (a*b*c) := by ring
    _ = _ := by rw [hc,inv_mul_cancel₀ hJ.ne',one_mul]

/-- Exact cancellation for three physical L³ norms, including field-valued
inputs in the fixed Euclidean fiber. -/
theorem inverseDual_L3_product_cancel {V : Type*} [NormedAddCommGroup V] (A : Space ≃L[ℝ] Space)
    {f g w : Space → V} (hf : MemLp f 3 volume) (hg : MemLp g 3 volume) (hw : MemLp w 3 volume) :
    let D := (physicalDualEquiv A).symm
    let F := (memLp_inverseDual_L3 A hf).toLp (f ∘ D)
    let G := (memLp_inverseDual_L3 A hg).toLp (g ∘ D)
    let W := (memLp_inverseDual_L3 A hw).toLp (w ∘ D)
    (linearJacobian A)⁻¹ * ‖F‖ * ‖G‖ * ‖W‖ = ‖hf.toLp f‖ * ‖hg.toLp g‖ * ‖hw.toLp w‖ := by
  dsimp only
  rw [inverseDual_toLp_L3_norm A hf,inverseDual_toLp_L3_norm A hg,inverseDual_toLp_L3_norm A hw]
  exact cancel_three_L3_scales (linearJacobian_pos A) _ _ _

theorem pullbackTrilinearFactor_L3_norm (A : Space ≃L[ℝ] Space) (f : SchwartzMap Space ℂ) :
    ‖(pullbackTrilinearFactor A f).toLp 3 volume‖ =
      (linearJacobian A)^(1/3 : ℝ) * ‖f.toLp 3 volume‖ := by
  have he : linearLpPullback (p := 3) (by norm_num) (physicalDualEquiv A).symm (f.toLp 3 volume) =
      (pullbackTrilinearFactor A f).toLp 3 volume :=
    linearLpPullback_toLp (by norm_num) (physicalDualEquiv A).symm (f.memLp 3 volume)
  rw [← he,inverseDual_linearLpPullback_L3_norm]

/-- The actual common null-chart dilation gives the manuscript's Fourier
identity and exact cancellation of its three L³ factors. -/
theorem parabolic_radianTrilinear_change {metric : Form} {u : Vec} (F : NullCapChart metric u)
    {δ : ℝ} (hδ : 0 < δ) (m : Joint → ℂ) (f g w : SchwartzMap Space ℂ)
    (hInt : Integrable (radianTrilinearWeight m f g w)) :
    let A := capFrequencyEquiv F hδ.ne'
    let J := δ^4 * linearJacobian (capFrameFrequencyEquiv F)
    let F' := pullbackTrilinearFactor A f
    let G' := pullbackTrilinearFactor A g
    let W' := pullbackTrilinearFactor A w
    Integrable (radianTrilinearWeight (m ∘ pairedFrequencyEquiv A) F' G' W') ∧
      radianTrilinearForm m f g w = J⁻¹ • radianTrilinearForm (m ∘ pairedFrequencyEquiv A) F' G' W' ∧
      J⁻¹ * ‖F'.toLp 3 volume‖ * ‖G'.toLp 3 volume‖ * ‖W'.toLp 3 volume‖ =
        ‖f.toLp 3 volume‖ * ‖g.toLp 3 volume‖ * ‖w.toLp 3 volume‖ := by
  dsimp only
  simp only [← linearJacobian_capFrequencyEquiv F hδ.ne']
  refine ⟨(integrable_radianTrilinearWeight_pairedFrequency_iff _ _ _ _ _).2 hInt,
    radianTrilinearForm_pairedFrequency _ _ _ _ _, ?_⟩
  rw [pullbackTrilinearFactor_L3_norm,pullbackTrilinearFactor_L3_norm,pullbackTrilinearFactor_L3_norm]
  exact cancel_three_L3_scales (linearJacobian_pos _) _ _ _

end Burnett.Analysis.CapFourier
