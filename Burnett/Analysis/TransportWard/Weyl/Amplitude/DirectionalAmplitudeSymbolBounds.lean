import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeWeightedInputJets

set_option autoImplicit false
set_option maxHeartbeats 5700000
noncomputable section

namespace Burnett.A03

open Finset Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology BigOperators

private def baseParameterProjection : RadianParameter →L[ℝ] RadianParameter :=
  (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E)

private def frequencyParameterProjection : RadianParameter →L[ℝ] RadianParameter :=
  (ContinuousLinearMap.inr ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)

/-- Choose the usual pure frequency directions at the indices in s
and pure base directions at the other indices. -/
def radianDirectionalParameterJet (f : RadianParameter → ℂ) (n : ℕ) (s : Finset (Fin n))
    (p : RadianParameter) : RadianParameterJet n ℂ :=
  (iteratedFDeriv ℝ n f p).compContinuousLinearMap
    (fun i => if i ∈ s then frequencyParameterProjection else baseParameterProjection)

theorem radian_scaled_parameter_jet_eq_directional_sum (f : RadianParameter → ℂ)
    (n : ℕ) (p : RadianParameter) :
    radianScaledParameterJet f n p = ∑ s : Finset (Fin n),
      radianFrequencyWeight p.2 ^ s.card • radianDirectionalParameterJet f n s p := by
  let scale := radianFrequencyWeight p.2
  let D := iteratedFDeriv ℝ n f p
  ext v
  let hf (i : Fin n) := frequencyParameterProjection (v i)
  let hb (i : Fin n) := baseParameterProjection (v i)
  let A (i : Fin n) := scale • hf i
  have split : (fun i => radianParameterScale scale (v i)) = A+hb := by
    funext i
    ext <;> simp [A,hf,hb,frequencyParameterProjection,baseParameterProjection]
  change D (fun i => radianParameterScale scale (v i)) =
    (∑ s : Finset (Fin n), scale^s.card • radianDirectionalParameterJet f n s p) v
  rw [split]
  have sum1 := D.toMultilinearMap.map_add_univ A hb
  change D (A+hb) = ∑ s : Finset (Fin n), D (s.piecewise A hb) at sum1
  rw [sum1]
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => RadianParameter) ℂ v
  change _ = L (∑ s : Finset (Fin n), scale^s.card • radianDirectionalParameterJet f n s p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  let a (i : Fin n) : ℝ := if i ∈ s then scale else 1
  have pieces : s.piecewise A hb = fun i => a i • (s.piecewise hf hb) i := by
    funext i
    by_cases hi : i ∈ s <;> simp [A,a,hi]
  have counts : (∏ i, a i) = scale^s.card := by
    dsimp only [a]
    rw [Finset.prod_ite_mem]
    simp only [Finset.univ_inter,Finset.prod_const]
  have v' : (fun i => (if i ∈ s then frequencyParameterProjection else baseParameterProjection) (v i)) =
      s.piecewise hf hb := by
    funext i
    by_cases hi : i ∈ s <;> simp [hf,hb,hi]
  have sc := D.toMultilinearMap.map_smul_univ a (s.piecewise hf hb)
  change D (fun i => a i • (s.piecewise hf hb) i) = (∏ i, a i) • D (s.piecewise hf hb) at sc
  rw [pieces,sc,counts]
  change _ = scale^s.card • D (fun i => (if i ∈ s then frequencyParameterProjection else baseParameterProjection) (v i))
  rw [v']

/-- Usual order-one estimates for all ordered choices of coordinate
directions, with the expected frequency derivative count. The
input-base derivatives occur before taking the norm. -/
def RadianOrdinaryDirectionalAmplitudeBounds (a : E → E → E → ℂ) : Prop :=
  ∀ n j : ℕ, ∀ s : Finset (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter, ∀ y : E,
    radianFrequencyWeight p.2 ^ s.card * ‖iteratedFDeriv ℝ j (fun z =>
      radianDirectionalParameterJet (radianTwoPointParameter a z) n s p) y‖ ≤ C*radianFrequencyWeight p.2

/-- The scaled joint input is a consequence of the ordinary directional
symbol estimates. The finite expansion is differentiated on the genuine
input-base variable of the same amplitude. -/
theorem compact_radian_scaled_order_one_of_directional
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry)
    (hs : RadianOrdinaryDirectionalAmplitudeBounds a) :
    CompactRadianScaledOrderOne a Rx Ry := by
  refine ⟨h,fun n j => ?_⟩
  choose B B0 Bb using hs n j
  use ∑ s : Finset (Fin n), B s,Finset.sum_nonneg (fun s _ => B0 s)
  intro p y
  let J (s : Finset (Fin n)) (z : E) := radianDirectionalParameterJet (radianTwoPointParameter a z) n s p
  let w (s : Finset (Fin n)) := radianFrequencyWeight p.2 ^ s.card
  let K (s : Finset (Fin n)) : RadianParameterJet n ℂ →L[ℝ] RadianParameterJet n ℂ :=
    ContinuousLinearMap.lsmul ℝ ℝ (w s)
  have d (s : Finset (Fin n)) : ContDiff ℝ ∞ (J s) := by
    let L := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
      (fun i : Fin n => if i ∈ s then frequencyParameterProjection else baseParameterProjection)
    change ContDiff ℝ ∞ (L ∘ fun z => iteratedFDeriv ℝ n (radianTwoPointParameter a z) p)
    exact L.contDiff.comp ((radian_two_point_parameter_jet_joint_smooth a Rx Ry h n).comp
      (contDiff_id.prodMk contDiff_const))
  have sc (s : Finset (Fin n)) :
      iteratedFDeriv ℝ j (K s ∘ J s) y = w s • iteratedFDeriv ℝ j (J s) y := by
    rw [(K s).iteratedFDeriv_comp_left (d s).contDiffAt (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
    rfl
  have lows : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have ep : (fun z => radianScaledParameterJet (radianTwoPointParameter a z) n p) =
      (fun z => ∑ s : Finset (Fin n), (K s ∘ J s) z) := by
    funext z
    exact radian_scaled_parameter_jet_eq_directional_sum (radianTwoPointParameter a z) n p
  have ds := iteratedFDeriv_sum (u := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun s => K s ∘ J s) (i := j) (𝕜 := ℝ)
    (fun s _ => ((K s).contDiff.comp (d s)).of_le lows)
  rw [ep,ds]
  simp only [Finset.sum_apply]
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [sc s,norm_smul,Real.norm_of_nonneg (pow_nonneg (radian_frequency_weight_pos p.2).le _)]
  exact Bb s p y

end Burnett.A03
