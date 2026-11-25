import Burnett.Analysis.AllScaleTransfer.GapBoxSeries
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric
open scoped ContDiff Manifold

/-- A finite atlas on the compact normalized annulus has fixed smooth
weights. Their quantitative bounds are chosen before the symbols or gaps. -/
theorem exists_box_chart_weights {ι : Type*} [Fintype ι] {K : Set BoxSpace}
    (hK : IsCompact K) (V : ι → Set BoxSpace) (hV : ∀ i, IsOpen (V i))
    (hCover : K ⊆ ⋃ i, V i) (P : ℝ) :
    ∃ (ρ : ι → BoxSpace → ℝ) (D : ℝ), 0 ≤ D ∧
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, tsupport (ρ i) ⊆ V i) ∧
      (∀ z ∈ K, ∑ i, ρ i z = 1) ∧
      ∀ i n, n ≤ 40 → ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (ρ i) z‖ ≤ D := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, BoxSpace) hK.isClosed V hV hCover
  have smooth (i : ι) : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
  have one (z : BoxSpace) (hz : z ∈ K) : ∑ i, ρ i z = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hz
  have bounded (i : ι × Fin 41) : ∃ B : ℝ, ∀ z ∈ closedBall (0 : BoxSpace) P,
      ‖iteratedFDeriv ℝ i.2.val (ρ i.1) z‖ ≤ B := by
    have hc := (smooth i.1).continuous_iteratedFDeriv
      (by exact_mod_cast (show i.2.val ≤ (⊤ : ℕ∞) from le_top))
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : BoxSpace) P).bddAbove_image hc.norm.continuousOn
    exact ⟨B, fun z hz => hB (mem_image_of_mem _ hz)⟩
  choose B hB using bounded
  let D := ∑ i : ι × Fin 41, max (B i) 0
  refine ⟨fun i => ρ i,D,Finset.sum_nonneg (fun i _ => le_max_right _ _),smooth,hρ,one,?_⟩
  intro i n hn z hz
  let k : ι × Fin 41 := (i,⟨n, by omega⟩)
  exact (hB k z hz).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => le_max_right (B j) 0) (Finset.mem_univ k)))

/-- The sum of the local box profiles using those fixed atlas weights
agrees with the original profile on the annular domain, with the same
finite-order geometric decay. -/
theorem weighted_atlas_box_profiles_sum {ι : Type*} [Fintype ι]
    (K : Set BoxSpace) (P : ℝ) (cutoff : ℕ) (ρ : ι → BoxSpace → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hOne : ∀ z ∈ K, ∑ i, ρ i z = 1)
    (hρJet : ∀ i n, n ≤ 40 → ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (ρ i) z‖ ≤ D)
    (G : ι → ℕ → BoxSpace → ℂ) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hG : ∀ i s, ContDiff ℝ 99 (G i s))
    (hGJet : ∀ i s n, n ≤ 40 → ∀ z ∈ closedBall (0 : BoxSpace) P,
      ‖iteratedFDeriv ℝ n (G i s) z‖ ≤ A i * radialGapDecay s)
    (original : ℕ → BoxSpace → ℂ)
    (hEq : ∀ i s, cutoff ≤ s → ∀ z ∈ K, ρ i z ≠ 0 → G i s z = original s z) :
    let profile (s : ℕ) (z : BoxSpace) := ∑ i, ρ i z • G i s z
    (∀ s, ContDiff ℝ 99 (profile s)) ∧
    (∀ s n, n ≤ 40 → ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (profile s) z‖ ≤
      ((2 : ℝ)^40 * D * ∑ i, A i) * radialGapDecay s) ∧
    ∀ s, cutoff ≤ s → ∀ z ∈ K, profile s z = original s z := by
  intro profile
  have smooth (i : ι) (s : ℕ) : ContDiff ℝ 99 (fun z => ρ i z • G i s z) :=
    ((hρ i).of_le (by decide : (99 : WithTop ℕ∞) ≤ ∞)).smul (hG i s)
  refine ⟨fun s => ContDiff.sum (fun i _ => smooth i s),?_,?_⟩
  · intro s n hn z hz
    have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hn.trans (by decide : (40 : ℕ) ≤ 99))
    have hTerm (i : ι) : ‖iteratedFDeriv ℝ n (fun z => ρ i z • G i s z) z‖ ≤
        (2 : ℝ)^40 * D * A i * radialGapDecay s := by
      have hProd := norm_iteratedFDeriv_smul_le ((hρ i).of_le (by decide : (99 : WithTop ℕ∞) ≤ ∞))
        (hG i s) z hn'
      refine hProd.trans ?_
      calc
        _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * D * (A i * radialGapDecay s) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hρJet i j (hj'.trans hn) z hz) (by positivity))
            (hGJet i s (n-j) ((Nat.sub_le n j).trans hn) z hz) (norm_nonneg _) (by positivity)
        _ = (2 : ℝ)^n * D * (A i * radialGapDecay s) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          norm_cast
          rw [Nat.sum_range_choose]
        _ ≤ (2 : ℝ)^40 * D * (A i * radialGapDecay s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hD)
            (mul_nonneg (hA i) (by unfold radialGapDecay; positivity))
        _ = _ := by ring
    have hd := iteratedFDeriv_sum (u := (Finset.univ : Finset ι)) (f := fun i z => ρ i z • G i s z)
      (i := n) (fun i _ => (smooth i s).of_le hn')
    change ‖iteratedFDeriv ℝ n (fun z => ∑ i, ρ i z • G i s z) z‖ ≤ _
    rw [hd, Finset.sum_apply]
    calc
      _ ≤ ∑ i, (2 : ℝ)^40 * D * A i * radialGapDecay s :=
        norm_sum_le_of_le _ (fun i _ => hTerm i)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  · intro s hs z hz
    calc
      profile s z = ∑ i, ρ i z • original s z := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : ρ i z = 0
        · simp only [h, zero_smul]
        · rw [hEq i s hs z hz h]
      _ = (∑ i, ρ i z) • original s z := by rw [Finset.sum_smul]
      _ = _ := by rw [hOne z hz, one_smul]

end Burnett.A05.BoxFourier
