import Burnett.Analysis.CenteredMaximal.MaximalLayerBound

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Filter
open scoped ENNReal

def maximalConstant (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^p*p) * 256 * ENNReal.ofReal (p-1)⁻¹

theorem maximalConstant_finite (p : ℝ) : maximalConstant p < ⊤ := by
  unfold maximalConstant
  finiteness

theorem centeredMax_moment_bounded (g : Space → ℝ) (hg : Measurable g) (hn : ∀ x,0≤g x)
    (H : ℝ) (hH : ∀ x, g x ≤ H) (p : ℝ) (hp : 1<p) :
    (∫⁻ x, (centeredMax (fun y => ENNReal.ofReal (g y)) x)^p) ≤
      maximalConstant p * ∫⁻ x, (ENNReal.ofReal (g x))^p := by
  let G := fun y => ENNReal.ofReal (g y)
  let M := centeredMax G
  let c : ℝ := (2:ℝ)^p*p
  have hp0 : 0<p := by linarith
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hp0
  have hM (x : Space) : M x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (centeredMax_le_const G (ENNReal.ofReal H) (fun y => ENNReal.ofReal_le_ofReal (hH y)) x)
  have left (x : Space) : (M x)^p = ENNReal.ofReal c * ENNReal.ofReal (((M x).toReal / 2)^p / p) := by
    rw [← ENNReal.ofReal_mul hc.le]
    calc
      _ = ENNReal.ofReal ((M x).toReal ^ p) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,ENNReal.ofReal_toReal (hM x)]
      _ = _ := by
        congr 1
        rw [Real.div_rpow ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        dsimp only [c]; field_simp [hp0.ne',(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p).ne']
  have right (x : Space) : ENNReal.ofReal (g x)*ENNReal.ofReal ((g x)^(p-1)/(p-1)) =
      ENNReal.ofReal (p-1)⁻¹ * (G x)^p := by
    rw [← ENNReal.ofReal_mul (hn x)]
    change _ = _ * (ENNReal.ofReal (g x))^p
    rw [ENNReal.ofReal_rpow_of_nonneg (hn x) hp0.le,← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_nonneg.mpr hp.le))]
    congr 1
    have hpow := Real.rpow_add_one' (x := g x) (y := p-1) (hn x) (by linarith)
    rw [sub_add_cancel] at hpow
    rw [hpow,div_eq_mul_inv]
    ring
  change (∫⁻ x, (M x)^p) ≤ maximalConstant p * ∫⁻ x, (G x)^p
  simp_rw [left]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h := maximal_layer_bound g hg hn H hH p hp
  simp_rw [right] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact (mul_le_mul_left' h (ENNReal.ofReal c)).trans_eq (by simp only [maximalConstant,c,mul_assoc])

end Burnett.Analysis.CenteredMaximal
