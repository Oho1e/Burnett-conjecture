import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 4800000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

section Jets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev RadianParameterJet (n : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => RadianParameter) V

/-- The actual joint Fréchet jet evaluated on frequency-normalized
directions at the given parameter point. -/
def radianScaledParameterJet (f : RadianParameter → V) (n : ℕ) (p : RadianParameter) :
    RadianParameterJet n V :=
  (iteratedFDeriv ℝ n f p).compContinuousLinearMap
    (fun _ => radianParameterScale (radianFrequencyWeight p.2))

theorem radian_parameter_jet_affine (f : RadianParameter → V)
    (h : ContDiff ℝ ∞ f) (n : ℕ) (p : RadianParameter) (s : ℝ) :
    iteratedFDeriv ℝ n (fun q => f (p+radianParameterScale s q)) 0 =
      (iteratedFDeriv ℝ n f p).compContinuousLinearMap (fun _ => radianParameterScale s) := by
  let L := radianParameterScale s
  let g (q : RadianParameter) := f (p+q)
  have c : ContDiff ℝ ∞ g := h.comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n (g ∘ L) 0 = _
  rw [L.iteratedFDeriv_comp_right c 0 (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp only [map_zero,g,iteratedFDeriv_comp_add_left,add_zero,L]

theorem radian_parameter_jet_norm_le_scaled (f : RadianParameter → V)
    (n : ℕ) (p : RadianParameter) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ ‖radianScaledParameterJet f n p‖ := by
  let s := radianFrequencyWeight p.2
  let L := radianParameterScale s⁻¹
  have sn : 1 ≤ s := radian_frequency_weight_one_le p.2
  have sp : 0 < s := radian_frequency_weight_pos p.2
  have Lb : ‖L‖ ≤ 1 := by
    exact (norm_radian_parameter_scale_le s⁻¹).trans (max_le le_rfl
      (by rw [Real.norm_of_nonneg (inv_nonneg.mpr sp.le)]; exact inv_le_one_of_one_le₀ sn))
  have split : iteratedFDeriv ℝ n f p =
      (radianScaledParameterJet f n p).compContinuousLinearMap (fun _ => L) := by
    ext v
    simp only [radianScaledParameterJet,ContinuousMultilinearMap.compContinuousLinearMap_apply,L,
      ← show s = radianFrequencyWeight p.2 from rfl,radian_parameter_scale_mul,
      mul_inv_cancel₀ sp.ne',radian_parameter_scale_one]
  calc
    _ = ‖(radianScaledParameterJet f n p).compContinuousLinearMap (fun _ => L)‖ := congrArg norm split
    _ ≤ ‖radianScaledParameterJet f n p‖ * ‖L‖^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (radianScaledParameterJet f n p).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) Lb)

end Jets

end Burnett.A03
