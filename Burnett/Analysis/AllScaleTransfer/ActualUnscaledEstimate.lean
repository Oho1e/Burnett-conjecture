import Burnett.Analysis.AllScaleTransfer.ActualUnscaledFirstLow
import Burnett.Analysis.AllScaleTransfer.ActualComparableBoxBound
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

set_option autoImplicit false
set_option maxHeartbeats 7600000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

/-- The three views of the same original Fourier symbol, in the cyclic
order that makes the designated low slot the first slot. -/
def radianLowSlotView (m : Joint → ℂ) (i : Fin 3) : Joint → ℂ :=
  ![m,m ∘ radianCycle.symm,m ∘ radianCycle] i

/-- The first assertion of the manuscript's all-scale estimate for the
actual unscaled Fourier form, with the given atlas and comparable boxes. -/
theorem exists_unscaled_radianTrilinearForm_bound {ι : Type*} [Fintype ι]
    (V : ι → Set FrequencyPair) (U : ι → Set LowRatio.Angles)
    (angular : ι → FrequencyPair → LowRatio.Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2 ⊆ ⋃ i, V i)
    (hAnn : ∀ i, V i ⊆ radialJetAnnulus (1/4) 3 ×ˢ radialJetAnnulus (1/4) 3)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i)) (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (rangeϑ : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (cutϑ : ∀ t, 1 ≤ t → ϑ t = 0) (flatϑ : ∀ t, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (l b : ℝ) (hl : 0 < l) (hub : 7*κ/4 < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (rangeχ : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (flatχ : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (cutχ : ∀ t, 7*κ/4 ≤ t → χ t = 0) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (m : Joint → ℂ) (B : ℝ), 0 ≤ B → Measurable m → (∀ p, ‖m p‖ ≤ B) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      ∀ D : ℝ, 0 ≤ D →
      let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0
      let comparable := radianFourBranchSymbol ϑ κ m 3
      (∀ slot : Fin 3, ∃ (M : ι → LowRatio.Point → ℂ) (M₀ : Joint → ℂ),
        (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) ∧
        (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
          ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) ∧
        (∀ i pq, pq ∈ V i →
          M₀ (endpointDirection pq.1,endpointDirection pq.2) = M i (angular i pq,0)) ∧
        ∀ i pq, pq ∈ V i → ∀ t : ℝ, 0 < t →
          let ρ := t*(‖pq.1‖/‖pq.2‖)
          ρ ∈ Ioo (0 : ℝ) b → low slot (t • pq.1,pq.2) = M i (angular i pq,ρ)) →
      (∃ G : ℤ → BoxSpace → ℂ,
        let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
        (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) ∧
        (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ D) ∧
        ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
          G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ)) →
      ∀ f g h : SchwartzMap E ℂ, ‖radianTrilinearForm m f g h‖ ≤ C*D*(triLpMass f g h 3 3 3).toReal := by
  classical
  let u := 7*κ/4
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by dsimp [u]; linarith only [hκsmall]
  obtain ⟨Clo,hClo,firstLow⟩ := exists_unscaled_radian_firstLow_bound V U angular hV hU hCover hAnn
    hAngular hMap l u b hl hu hu1 hub χ hχ rangeχ flatχ cutχ
  obtain ⟨N,Cco,hCco,compare⟩ := exists_radianComparable_box_bound cutϑ flatϑ
    5 κ 1 1 (by norm_num) hκ hκsmall zero_lt_one zero_lt_one
  refine ⟨N,3*Clo+Cco,by positivity,?_⟩
  intro m B hB hm bM hom D hD low comparable charts boxes f g h
  have cyc : ∀ (t : ℝ) (p : Joint), radianCycle (t • p) = t • radianCycle p := by
    intro t p
    apply Prod.ext
    · rfl
    · change -(t • p.1+t • p.2) = t • (-(p.1+p.2))
      rw [smul_neg,smul_add]
  have cycsymm : ∀ (t : ℝ) (p : Joint), radianCycle.symm (t • p) = t • radianCycle.symm p := by
    intro t p
    apply Prod.ext
    · change -(t • p.1+t • p.2) = t • (-(p.1+p.2))
      rw [smul_neg,smul_add]
    · rfl
  have viewsMeas (i : Fin 3) : Measurable (radianLowSlotView m i) := by
    fin_cases i
    · exact hm
    · exact hm.comp radianCycle.symm.measurable
    · exact hm.comp radianCycle.measurable
  have viewsHom (i : Fin 3) (t : ℝ) (ht : 0 < t) (p : Joint) :
      radianLowSlotView m i (t • p) = radianLowSlotView m i p := by
    fin_cases i
    · exact hom t ht p
    · change m (radianCycle.symm (t • p)) = m (radianCycle.symm p)
      rw [cycsymm,hom t ht]
    · change m (radianCycle (t • p)) = m (radianCycle p)
      rw [cyc,hom t ht]
  have viewsBound (i : Fin 3) (p : Joint) : ‖low i p‖ ≤ B := by
    change ‖(lowSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) : ℂ) * radianLowSlotView m i p‖ ≤ B
    rw [norm_mul,Complex.norm_real]
    have r : ‖lowSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2))‖ ≤ 1 := rangeϑ _ (by positivity)
    let x := radianLowSlotView m i p
    calc
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right r (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ ≤ B := by
        change ‖radianLowSlotView m i p‖ ≤ B
        fin_cases i
        · exact bM p
        · exact bM (radianCycle.symm p)
        · exact bM (radianCycle p)
  have lo (i : Fin 3) (x y z : SchwartzMap E ℂ) :
      ‖radianTrilinearForm (low i) x y z‖ ≤ Clo*D*(triLpMass x y z 3 3 3).toReal := by
    obtain ⟨M,M₀,smooth,jets,trace,source⟩ := charts i
    exact firstLow M M₀ D hD smooth jets trace (low i) B hB
      (measurable_radianFourBranchSymbol ϑ hϑ κ _ (viewsMeas i) 0) (viewsBound i)
      (radianFourBranchSymbol_homogeneous ϑ κ _ (viewsHom i) 0)
      (radianFourBranchSymbol_first_low_ratio ϑ cutϑ hκ hκsmall _) source x y z
  have coSupport (p : Joint) (hp : comparable p ≠ 0) :
      comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) ≠ 0 := by
    intro hz
    apply hp
    change ((comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) : ℝ) : ℂ) * m p = 0
    rw [hz,Complex.ofReal_zero,zero_mul]
  obtain ⟨G,sG,bG,eG⟩ := boxes
  have co := compare (ContinuousLinearEquiv.refl ℝ E) comparable
    (fun p hp => ⟨coSupport p hp,by simp,by simp,by simp⟩)
    (radianFourBranchSymbol_homogeneous ϑ κ m hom 3)
    (measurable_radianFourBranchSymbol ϑ hϑ κ m hm 3).aestronglyMeasurable
    G D hD sG bG eG f g h
  calc
    _ ≤ (Clo*D+Clo*D+Clo*D+Cco*D)*(triLpMass f g h 3 3 3).toReal :=
      radianTrilinearForm_bound_of_four_branch_estimates ϑ hϑ rangeϑ κ m hm B bM f g h
        (Clo*D) (Clo*D) (Clo*D) (Cco*D) (lo 0 f g h) (lo 1 g h f) (lo 2 h f g) co
    _ = _ := by ring

end Burnett.A05
