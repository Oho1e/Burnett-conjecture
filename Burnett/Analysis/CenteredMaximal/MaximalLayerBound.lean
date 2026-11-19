import Burnett.Analysis.CenteredMaximal.MaximalDistribution

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Filter Set Metric
open scoped ENNReal

theorem centeredMax_le_const (g : Space → ℝ≥0∞) (c : ℝ≥0∞) (hc : ∀ y, g y ≤ c) (x : Space) :
    centeredMax g x ≤ c := by
  apply iSup_le
  intro r
  apply (ENNReal.div_le_iff_le_mul (.inl (measure_closedBall_pos volume x r.2).ne')
    (.inl measure_closedBall_lt_top.ne)).mpr
  exact (lintegral_mono hc).trans_eq (by rw [lintegral_const,Measure.restrict_apply_univ])

/-- Strong maximal estimate in power-integral form, with the two harmless
normalization factors from integration of heights displayed separately. -/
theorem maximal_layer_bound (g : Space → ℝ) (hg : Measurable g) (hn : ∀ x,0≤g x)
    (H : ℝ) (hH : ∀ x, g x ≤ H) (p : ℝ) (hp : 1<p) :
    (∫⁻ x, ENNReal.ofReal (((centeredMax (fun y => ENNReal.ofReal (g y)) x).toReal / 2)^p / p)) ≤
      256 * ∫⁻ x, ENNReal.ofReal (g x)*ENNReal.ofReal ((g x)^(p-1)/(p-1)) := by
  let G := fun y => ENNReal.ofReal (g y)
  let M := centeredMax G
  have hM (x : Space) : M x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (centeredMax_le_const G (ENNReal.ofReal H) (fun y => ENNReal.ofReal_le_ofReal (hH y)) x)
  let f := fun x => (M x).toReal / 2
  have hf : Measurable f := (centeredMax_measurable G).ennreal_toReal.div_const _
  have hfn (x : Space) : 0 ≤ f x := div_nonneg ENNReal.toReal_nonneg (by norm_num)
  change (∫⁻ x, ENNReal.ofReal ((f x)^p / p)) ≤ _
  rw [power_distribution volume f hf hfn p (by linarith),← integrated_tail_power g hg hn (p-1) (by linarith)]
  rw [← lintegral_const_mul' (256:ℝ≥0∞) _ (by norm_num)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  have pos : 0<t := ht
  have levelEq : {x | t < f x} = {x | 2*ENNReal.ofReal t < M x} := by
    ext x
    change t < (M x).toReal / 2 ↔ 2 * ENNReal.ofReal t < M x
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hM x)]
    constructor <;> intro h <;> linarith
  have hpow : ENNReal.ofReal (t^(p-1)) = ENNReal.ofReal t * ENNReal.ofReal (t^(p-1-1)) := by
    rw [← ENNReal.ofReal_mul pos.le,show p-1=(p-1-1)+1 by ring,Real.rpow_add_one pos.ne']
    congr 1
    ring_nf
  rw [levelEq,hpow]
  calc
    _ = (ENNReal.ofReal t * volume {x | 2*ENNReal.ofReal t < M x}) * ENNReal.ofReal (t^(p-1-1)) := by ac_rfl
    _ ≤ (256 * (∫⁻ y, upperTail G (ENNReal.ofReal t) y)) * ENNReal.ofReal (t^(p-1-1)) :=
      mul_le_mul_right' (centeredMax_tail G (ENNReal.ofReal t)) _
    _ = _ := by ac_rfl

end Burnett.Analysis.CenteredMaximal
