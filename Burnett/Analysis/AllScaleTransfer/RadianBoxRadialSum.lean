import Burnett.Analysis.AllScaleTransfer.RadianBoxBlock
import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A03 (spatialLatticeVector)
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight)
open scoped Topology

theorem radianTrilinearForm_const_mul (c : ℂ) (m : Joint → ℂ) (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm (fun p => c * m p) f g h = c * radianTrilinearForm m f g h := by
  unfold radianTrilinearForm radianTrilinearWeight
  simp only [mul_assoc, integral_const_mul, Algebra.smul_def]
  ring

/-- The mode expansion of the same radial block sum is taken in the genuine
trilinear Fourier integral. Pointwise radial overlap bounds the whole mode
family by a fixed window constant times the summable coefficient masses. -/
theorem hasSum_radianTrilinearForm_radial_box_modes
    (P : ℝ) (hP : 0 < P) (a b d f g h : SchwartzMap E ℂ)
    (t u : ℝ) (ht : 0 < t) (v : ℤ → ℝ)
    (ha : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (G : BoxSpace → ℂ) (c : FourierModePair → ℂ) (hc : Summable fun k => ‖c k‖)
    (hSeries : ∀ ζ υ : E, a ζ ≠ 0 → b υ ≠ 0 →
      HasSum (fun k => c k * separatedBoxMode P k (joinedInputs ζ υ)) (G (joinedInputs ζ υ))) :
    let Z (j : ℤ) := radianBoxBlock a b d ((2 : ℝ)^(-j) * t) ((2 : ℝ)^(-j) * u) (v j) G
    let R (k : FourierModePair) (j : ℤ) := radianSeparatedWindowSymbol a b d
      ((2 : ℝ)^(-j) * t) ((2 : ℝ)^(-j) * u) (v j)
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2)
    HasSum (fun k => c k * radianTrilinearForm (fun p => ∑' j, R k j p) f g h)
      (radianTrilinearForm (fun p => ∑' j, Z j p) f g h) := by
  intro Z R
  let A (j : ℤ) (p : Joint) := a (((2 : ℝ)^(-j) * t) • (tau⁻¹ • p.1))
  have hLoc (p : Joint) : ∃ I : Finset ℤ, I.card ≤ 3 ∧ ∀ j ∉ I, A j p = 0 := by
    let ρ := t * ‖tau⁻¹ • p.1‖
    obtain ⟨I,hI,hAnn⟩ := exists_integer_radial_annulus_indices ρ
    refine ⟨I,hI,?_⟩
    intro j hj
    by_contra h
    have hn := ha _ h
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) _),
      Real.norm_of_nonneg ht.le, mul_assoc] at hn
    exact hj (hAnn j hn.1 hn.2)
  have hZ (j : ℤ) (p : Joint) (hzero : A j p = 0) : Z j p = 0 := by
    change a (((2 : ℝ)^(-j) * t) • (tau⁻¹ • p.1)) = 0 at hzero
    simp only [Z, radianBoxBlock, hzero, zero_mul, mul_zero]
  have hR (k : FourierModePair) (j : ℤ) (p : Joint) (hzero : A j p = 0) : R k j p = 0 := by
    change a (((2 : ℝ)^(-j) * t) • (tau⁻¹ • p.1)) = 0 at hzero
    simp only [R, radianSeparatedWindowSymbol_eq_boxMode P hP, radianBoxBlock, hzero, zero_mul, mul_zero]
  let B := SchwartzMap.seminorm ℝ 0 0 a * SchwartzMap.seminorm ℝ 0 0 b *
    SchwartzMap.seminorm ℝ 0 0 d
  have hB : 0 ≤ B := by unfold B; positivity
  have hCont (k : FourierModePair) (j : ℤ) : Continuous (R k j) :=
    continuous_radianBoxBlock_mode P hP a b d _ _ _ k
  have hMeas (k : FourierModePair) : Measurable (fun p => ∑' j, R k j p) := by
    apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
      (f := fun I p => ∑ j ∈ I, R k j p)
    · intro I
      exact (continuous_finset_sum I (fun j _ => hCont k j)).measurable
    · rw [tendsto_pi_nhds]
      intro p
      obtain ⟨I,_,hI⟩ := hLoc p
      have hSum : HasSum (fun j => R k j p) (∑' j, R k j p) :=
        (summable_of_ne_finset_zero (fun j hj => hR k j p (hI j hj))).hasSum
      exact hSum
  have hBound (k : FourierModePair) (p : Joint) : ‖∑' j, R k j p‖ ≤ 3 * B := by
    obtain ⟨I,hI,hzero⟩ := hLoc p
    rw [tsum_eq_sum (s := I) (fun j hj => hR k j p (hzero j hj))]
    calc
      _ ≤ ∑ j ∈ I, B := norm_sum_le_of_le _ fun j _ => norm_radianBoxBlock_mode_le P hP a b d _ _ _ k p
      _ = (I.card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hB
  have hPoint (p : Joint) : HasSum (fun k => c k * ∑' j, R k j p) (∑' j, Z j p) := by
    obtain ⟨I,_,hzero⟩ := hLoc p
    have hRsum (k : FourierModePair) : (∑' j, R k j p) = ∑ j ∈ I, R k j p :=
      tsum_eq_sum (fun j hj => hR k j p (hzero j hj))
    rw [tsum_eq_sum (s := I) (fun j hj => hZ j p (hzero j hj))]
    simp only [hRsum, Finset.mul_sum]
    have hAt (j : ℤ) (_ : j ∈ I) : HasSum (fun k => c k * R k j p) (Z j p) :=
      hasSum_radianBoxBlock_modes_at P hP a b d _ _ _ G c hSeries p
    simpa only [Finset.sum_fn] using hasSum_sum hAt
  let F (k : FourierModePair) (p : Joint) := c k * ∑' j, R k j p
  have hF (k : FourierModePair) : AEStronglyMeasurable (F k) volume :=
    ((hMeas k).const_mul (c k)).aestronglyMeasurable
  have hMaj (k : FourierModePair) (p : Joint) : ‖F k p‖ ≤ ‖c k‖ * (3 * B) := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hBound k p) (norm_nonneg _)
  have result := radianTrilinearForm_hasSum_of_symbol_expansion F (fun p => ∑' j, Z j p)
    (fun k => ‖c k‖ * (3 * B)) hF (hc.mul_right _) hMaj (Eventually.of_forall hPoint) f g h
  simpa only [F, radianTrilinearForm_const_mul] using result

end Burnett.A05
