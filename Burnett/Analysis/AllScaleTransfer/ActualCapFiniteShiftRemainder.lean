import Burnett.Analysis.AllScaleTransfer.ActualFiniteShiftRemainder
import Burnett.Analysis.AllScaleTransfer.ActualCapDyadicRemainderTail

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal

private theorem original_signedAxis_pos {α : ℝ} (hα : 0 < α)
    (p : Frequency) (i : ℤ) (sign : Bool) (hp : ((2 : ℝ)^(-i)) • p ∈ signedClosedAnnulus α sign) :
    0 < signedAxis sign p := by
  have hNorm : 0 < ‖((2 : ℝ)^(-i)) • p‖ := (by norm_num : (0 : ℝ) < 1/2).trans_le hp.1.1
  have hAxis : 0 < signedAxis sign (((2 : ℝ)^(-i)) • p) :=
    (mul_pos hα hNorm).trans_le hp.2
  have he (t : ℝ) : signedAxis sign (t • p) = t * signedAxis sign p := by
    cases sign
    · change -(t * p 0) = t * -(p 0)
      ring
    · rfl
  rw [he] at hAxis
  exact pos_of_mul_pos_right hAxis (by positivity)

/-- The finite remainder shifts on an actual enlarged cap. The same A
supplies the normalized coordinates, the radial jets and the third window.
The four signed boxes cover the actual clipped Fourier inputs. -/
theorem exists_actual_cap_finite_shift_remainder_bound
    (I : Finset ℤ) (B tube outer enlarged u b : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hu : 0 < u) (hu1 : u < 1) (hub : u < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1) :
    ∃ (R C : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ C ∧
      ∀ (m₀ : Form) (w : Vec) (F : NullCapChart m₀ w),
        ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4 * B * (5 * δ) ≤ 1 →
          let A := capFrequencyEquiv F hδ.ne'
          let P := tsupport (enlargedCapMultiplier m₀ δ (tube*δ^2) outer enlarged w)
          let O := ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R
          let W := O ×ˢ Ico (0 : ℝ) b
          ∀ (M : CapSigns → LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
            (∀ signs, ContDiffOn ℝ 100 (M signs) W) →
            (∀ signs n, n ≤ 100 → ∀ z ∈ W, ‖iteratedFDerivWithin ℝ n (M signs) W z‖ ≤ A₁₀₀) →
            ∀ (m : Joint → ℂ) (f g h : SchwartzMap E ℂ),
            (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → A p.1 ∈ P ∧ A p.2 ∈ P) →
            (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → m p ≠ 0 → ‖A p.1‖ / ‖A p.2‖ ≤ u) →
            (∀ signs (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
              0 < signedAxis signs.1 p.1 → 0 < signedAxis signs.2 p.2 →
              let ρ := ‖A p.1‖ / ‖A p.2‖
              ρ ∈ Ioo (0 : ℝ) b → m p = ρ • LowRatio.remainder (M signs) χ
                ((endpointTail (endpointDirection p.1), endpointTail (endpointDirection p.2)), ρ)) →
            let J (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol m k) f g h
            let Mass := (triLpMass f g h 3 3 3).toReal
            (∀ k ∈ I, ‖J k‖ ≤ C * A₁₀₀ * Mass) ∧
            ‖∑ k ∈ I, J k‖ ≤ (I.card : ℝ) * C * A₁₀₀ * Mass := by
  obtain ⟨α,r,R,hα,_,hr,hrR,hR,hCharts,hCover⟩ :=
    exists_actual_cap_signed_annular_boxes B tube outer enlarged hB hTube hOut hOE
  let O := ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R
  have hO : IsOpen O := isOpen_ball.prod isOpen_ball
  obtain ⟨J,hJ,bCap⟩ :=
    exists_uniform_capFrequency_radial_seminorms B tube outer enlarged (α/2) (1/4) 3
      hB hTube hOut hOE (half_pos hα) (by norm_num) 40
  have nz (signs : CapSigns) (pq : FrequencyPair) (hp : pq ∈ signedPairV α signs) :
      pq.1 ≠ 0 ∧ pq.2 ≠ 0 := by
    have h := (hCharts signs).2.2.2.1 hp
    exact ⟨norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans_le h.1.1.1),
      norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans_le h.2.1.1)⟩
  have mk (signs : CapSigns) := exists_finite_shift_remainder_boxes I J hJ.le
    (hCharts signs).1 (hCharts signs).2.1 (hCharts signs).2.2.1 (nz signs) hO
    (normalizedPairAngles endpointTail endpointTail)
    (normalizedPairAngles_contDiffOn endpointTail endpointTail (nz signs))
    (hCharts signs).2.2.2.2 hu hub χ hχ
  choose η D hD oneη zeroη data using mk
  obtain ⟨L,_,hL,_,hNorm⟩ :=
    exists_uniform_capFrequency_norm_compare B tube outer enlarged hB hTube hOut hOE
  let U := B * ‖frequencyCoordinates.toContinuousLinearMap‖ + 1
  have hU : 0 < U := by dsimp [U]; positivity
  obtain ⟨_,Cbox,hCbox,box⟩ := exists_finite_shift_remainder_bound_of_profiles I L U u hL hU hu hu1
  let Dsum := ∑ signs : CapSigns, D signs
  have hDsum : 0 ≤ Dsum := Finset.sum_nonneg (fun signs _ => hD signs)
  refine ⟨R,Cbox*Dsum,hr.trans hrR,hR,mul_nonneg hCbox hDsum,?_⟩
  intro m₀ w F hw hF hFI δ hδ hδOne hδSmall A P O' W M A₁₀₀ hA sM bM m f g h hSupp hRatio hSymbol J' Mass
  obtain ⟨_,bPair⟩ := bCap m₀ w F hw hF hFI δ hδ hδOne hδSmall
  have chart (signs : CapSigns) := data signs A (fun n hn pq hpq => by
    have hq := (hCharts signs).2.2.2.1 hpq
    exact (bPair n hn pq.1 ⟨hq.1.1,Or.inl hq.1.2⟩ pq.2 ⟨hq.2.1,Or.inl hq.2.2⟩).1)
    (M signs) A₁₀₀ hA (sM signs) (bM signs)
  choose G sG zG bG eG using chart
  let Gsum (k : ℤ) (z : BoxSpace) : ℂ := ∑ signs : CapSigns, G signs k z
  have sGsum (k : ℤ) : ContDiff ℝ 100 (Gsum k) := ContDiff.sum (fun signs _ => sG signs k)
  have bGsum (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (z : BoxSpace) :
      ‖iteratedFDeriv ℝ n (Gsum k) z‖ ≤ Dsum * A₁₀₀ := by
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 100))
    have H := iteratedFDeriv_sum (u := (Finset.univ : Finset CapSigns)) (f := fun signs => G signs k)
      (i := n) (fun signs _ => (sG signs k).of_le hn')
    change ‖iteratedFDeriv ℝ n (fun x => ∑ signs : CapSigns, G signs k x) z‖ ≤ _
    rw [H, Finset.sum_apply]
    calc
      _ ≤ ∑ signs : CapSigns, D signs * A₁₀₀ :=
        norm_sum_le_of_le _ (fun signs _ => bG signs k hk n hn z)
      _ = _ := (Finset.sum_mul ..).symm
  have hUpper (p : Frequency) : ‖A p‖ ≤ U * ‖p‖ := by
    have hOp := capFrequencyEquiv_opNorm_le F hδ hδOne hB.le hF
    exact (A.toContinuousLinearMap.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right (hOp.trans (by dsimp [U]; linarith)) (norm_nonneg _))
  have hActive (p : Joint) (hW : radianWeight (fun _ => 1) f g h p ≠ 0) (hm : m p ≠ 0) :
      L * ‖p.1‖ ≤ ‖A p.1‖ ∧ L * ‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u :=
    ⟨(hNorm m₀ w F hw hFI δ hδ hδSmall p.1 (hSupp p hW).1).1,
      (hNorm m₀ w F hw hFI δ hδ hδSmall p.2 (hSupp p hW).2).1,hRatio p hW hm⟩
  have eq (k : ℤ) (_hk : k ∈ I) (j : ℤ) (p : Joint) (hW : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hl : integerRadialWindow (j+k) p.1 ≠ 0) (hq : integerRadialWindow j p.2 ≠ 0) :
      Gsum k (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) = m p := by
    let ζ := ((2 : ℝ)^(-(j+k))) • p.1
    let υ := ((2 : ℝ)^(-j)) • p.2
    let z := joinedInputs ζ υ
    let ρ := ‖A p.1‖ / ‖A p.2‖
    obtain ⟨signs,hKz,_⟩ := hCover m₀ w F hw hFI δ hδ hδSmall
      (j+k) j p.1 p.2 hl hq (hSupp p hW).1 (hSupp p hW).2
    change boxToPair z ∈ signedPairK α signs at hKz
    have hK : (ζ,υ) ∈ signedPairK α signs := by simpa only [z,boxToPair_joined] using hKz
    have hSign1 := original_signedAxis_pos hα p.1 (j+k) signs.1 hK.1
    have hSign2 := original_signedAxis_pos hα p.2 j signs.2 hK.2
    have hρPos : 0 < ρ := by
      have hn (l : ℤ) (x : E) (hx : integerRadialWindow l x ≠ 0) : 0 < ‖A x‖ := by
        have hx' : x ≠ 0 := fun hz => hx (by rw [hz, integerRadialWindow_zero])
        exact norm_pos_iff.mpr (fun hz => hx' (A.injective (hz.trans A.map_zero.symm)))
      exact div_pos (hn _ _ hl) (hn _ _ hq)
    have hUnique : Gsum k z = G signs k z := by
      unfold Gsum
      refine Finset.sum_eq_single signs ?_ (by simp)
      intro other _ hne
      exact zG other k z (signedPairK_notMem_other_signedPairV hα (Ne.symm hne) hKz)
    have hAng : normalizedPairAngles endpointTail endpointTail (ζ,υ) =
        (endpointTail (endpointDirection p.1), endpointTail (endpointDirection p.2)) := by
      simpa only [boxToPair_joined] using normalized_signed_box_angles (j+k) j p.1 p.2
    change Gsum k z = m p
    rw [hUnique]
    change G signs k (joinedInputs ζ υ) = m p
    rw [eG signs k ζ υ hK,
      fixedShiftPhysicalRatio_at_frequencies A k j p.1 p.2,hAng]
    by_cases hρb : ρ < b
    · rw [cutoffRemainderNumerator_eq_ratio_remainder _ _ _ hχ0]
      change η signs ρ • (ρ • LowRatio.remainder (M signs) χ
        ((endpointTail (endpointDirection p.1),endpointTail (endpointDirection p.2)),ρ)) = m p
      rw [← hSymbol signs p hW hSign1 hSign2 ⟨hρPos,hρb⟩]
      by_cases hm : m p = 0
      · rw [hm, smul_zero]
      · rw [oneη signs ρ ⟨hρPos.le,hRatio p hW hm⟩, one_smul]
    · have hm : m p = 0 := by
        by_contra hn
        exact hρb ((hRatio p hW hn).trans_lt hub)
      have hη := zeroη signs ρ (le_of_not_gt hρb)
      change η signs ρ • _ = m p
      rw [hη, zero_smul, hm]
  have out := box A hUpper m Gsum (Dsum*A₁₀₀) (mul_nonneg hDsum hA)
    (fun k _ => (sGsum k).contDiffOn) (fun k hk n hn z _ => bGsum k hk n hn z)
    f g h hActive eq
  exact ⟨fun k hk => by simpa only [mul_assoc] using (out.1 k hk).2,
    by simpa only [mul_assoc] using out.2⟩

end Burnett.A05.BoxFourier
