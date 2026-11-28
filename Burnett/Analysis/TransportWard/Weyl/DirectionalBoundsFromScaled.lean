import Burnett.Analysis.TransportWard.Weyl.Amplitude.DirectionalAmplitudeSymbolBounds

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section

namespace Burnett.A03

open Function Set
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators ContDiff

open private baseParameterProjection frequencyParameterProjection from Burnett.Analysis.TransportWard.Weyl.Amplitude.DirectionalAmplitudeSymbolBounds

/-- Restricting the genuine scaled jet to ordered pure coordinate directions
recovers the directional estimates with their exact frequency weights. -/
theorem radianOrdinaryDirectionalAmplitudeBounds_of_scaled
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianScaledOrderOne a Rx Ry) :
    RadianOrdinaryDirectionalAmplitudeBounds a := by
  intro n j s
  obtain ⟨C, hC, hBound⟩ := h.scaledInputJetEstimate n j
  refine ⟨C, hC, fun p y => ?_⟩
  let W := radianFrequencyWeight p.2
  let P (i : Fin n) : RadianParameter →L[ℝ] RadianParameter :=
    if i ∈ s then frequencyParameterProjection else baseParameterProjection
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ) P
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ) (fun _ : Fin n => radianParameterScale W)
  let K : RadianParameterJet n ℂ →L[ℝ] RadianParameterJet n ℂ := ContinuousLinearMap.lsmul ℝ ℝ (W ^ s.card)
  let Z (z : E) := radianScaledParameterJet (radianTwoPointParameter a z) n p
  let J (z : E) := radianDirectionalParameterJet (radianTwoPointParameter a z) n s p
  have hP (i : Fin n) : ‖P i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    by_cases hi : i ∈ s
    · simp [P, hi, frequencyParameterProjection, Prod.norm_def]
    · simp [P, hi, baseParameterProjection, Prod.norm_def]
  have hL : ‖L‖ ≤ 1 :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℂ P).trans
      (Finset.prod_le_one (fun i _ => norm_nonneg (P i)) (fun i _ => hP i))
  have hSmooth : ContDiff ℝ ∞ (fun z : E => iteratedFDeriv ℝ n (radianTwoPointParameter a z) p) :=
    (radian_two_point_parameter_jet_joint_smooth a Rx Ry h.toCompactRadianTwoPointOrderOne n).comp
      (contDiff_id.prodMk contDiff_const)
  have hZ : ContDiff ℝ ∞ Z := T.contDiff.comp hSmooth
  have hJ : ContDiff ℝ ∞ J := L.contDiff.comp hSmooth
  have hI : L ∘ Z = K ∘ J := by
    funext z
    ext v
    let D := iteratedFDeriv ℝ n (radianTwoPointParameter a z) p
    let c (i : Fin n) : ℝ := if i ∈ s then W else 1
    have hDir (i : Fin n) : radianParameterScale W (P i (v i)) = c i • P i (v i) := by
      by_cases hi : i ∈ s <;> apply Prod.ext <;>
        simp [P,c,hi,baseParameterProjection,frequencyParameterProjection]
    have hMul : (∏ i, c i) = W ^ s.card := by
      dsimp only [c]
      rw [Finset.prod_ite_mem]
      simp only [Finset.univ_inter, Finset.prod_const]
    change D (fun i => radianParameterScale W (P i (v i))) = W ^ s.card • D (fun i => P i (v i))
    have hScaling := D.toMultilinearMap.map_smul_univ c (fun i => P i (v i))
    change D (fun i => c i • P i (v i)) = (∏ i, c i) • D (fun i => P i (v i)) at hScaling
    rw [funext hDir, hScaling, hMul]
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hDiff : (W ^ s.card) • iteratedFDeriv ℝ j J y =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ j Z y) := by
    rw [← L.iteratedFDeriv_comp_left hZ.contDiffAt hj, hI,
      K.iteratedFDeriv_comp_left hJ.contDiffAt hj]
    rfl
  change W ^ s.card * ‖iteratedFDeriv ℝ j J y‖ ≤ C * W
  rw [← Real.norm_of_nonneg (pow_nonneg (radian_frequency_weight_pos p.2).le s.card), ← norm_smul, hDiff]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hBound p y))

end Burnett.A03
