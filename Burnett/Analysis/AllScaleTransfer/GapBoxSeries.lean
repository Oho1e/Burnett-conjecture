import Burnett.Analysis.AllScaleTransfer.JointCubeReconstruction
import Burnett.Analysis.AllScaleTransfer.JointModeDecay
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.A05.BoxFourier

open MeasureTheory Set Metric Filter Burnett.A03
open scoped ContDiff Topology

private theorem cutoff_forty_jets (χ : BoxSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (P : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≤ 40, ∀ z ∈ closedBall (0 : BoxSpace) P,
      ‖iteratedFDeriv ℝ n χ z‖ ≤ K := by
  have bounded (n : Fin 41) :
      ∃ B : ℝ, ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n.val χ z‖ ≤ B := by
    have hc : Continuous (iteratedFDeriv ℝ n.val χ) :=
      hχ.continuous_iteratedFDeriv (by exact_mod_cast (show n.val ≤ (⊤ : ℕ∞) from le_top))
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : BoxSpace) P).bddAbove_image hc.norm.continuousOn
    exact ⟨B, fun z hz => hB (mem_image_of_mem _ hz)⟩
  choose B hB using bounded
  refine ⟨∑ n : Fin 41, max (B n) 0, Finset.sum_nonneg fun n _ => le_max_right _ _, ?_⟩
  intro n hn z hz
  let i : Fin 41 := ⟨n, by omega⟩
  exact (hB i z hz).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => le_max_right (B j) 0) (Finset.mem_univ i)))

private theorem cutoff_profile_forty_jets (P : ℝ) (χ : BoxSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupport : tsupport χ ⊆ ball (0 : BoxSpace) P)
    (g : BoxSpace → ℂ) (hg : ContDiffOn ℝ 40 g (ball (0 : BoxSpace) P))
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (bχ : ∀ n ≤ 40, ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n χ z‖ ≤ K)
    (bg : ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n g z‖ ≤ M) :
    ContDiff ℝ 40 (fun z => χ z • g z) ∧
      ∀ n ≤ 40, ∀ z : BoxSpace, ‖iteratedFDeriv ℝ n (fun w => χ w • g w) z‖ ≤ (2 : ℝ)^40 * K * M := by
  let U := ball (0 : BoxSpace) P
  let f (z : BoxSpace) := χ z • g z
  have finiteOrder (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have hχ40 : ContDiffOn ℝ 40 χ U := (hχ.of_le (finiteOrder 40)).contDiffOn
  have hLoc : ContDiffOn ℝ 40 f U := hχ40.smul hg
  have outside (z : BoxSpace) (hz : z ∉ U) : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hχSupport h))] with x hx
    change χ x = 0 at hx
    simp [f, hx]
  refine ⟨contDiff_iff_contDiffAt.mpr (fun z => ?_), ?_⟩
  · by_cases hz : z ∈ U
    · exact hLoc.contDiffAt (isOpen_ball.mem_nhds hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (outside z hz)
  intro n hn z
  by_cases hz : z ∈ U
  · have hn' : (n : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hn
    have e (f : BoxSpace → ℂ) (i : ℕ) :
        iteratedFDerivWithin ℝ i f U z = iteratedFDeriv ℝ i f z :=
      iteratedFDerivWithin_of_isOpen i isOpen_ball hz
    rw [← e f n]
    refine (norm_iteratedFDerivWithin_smul_le hχ40 hg isOpen_ball.uniqueDiffOn hz hn').trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K * M := by
        apply Finset.sum_le_sum
        intro i hi
        have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen i isOpen_ball hz, e g (n - i)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (bχ i (hile.trans hn) z (ball_subset_closedBall hz))
            (by positivity))
          (bg (n - i) ((Nat.sub_le n i).trans hn) z hz) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^n * K * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hK) hM
  · have hf : z ∉ tsupport f := notMem_tsupport_iff_eventuallyEq.mpr (outside z hz)
    have hJet : iteratedFDeriv ℝ n f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hf (tsupport_iteratedFDeriv_subset n h))
    rw [hJet, norm_zero]
    positivity

theorem one_le_modePairLoss (ab : FourierModePair) : 1 ≤ modePairLoss ab := by
  unfold modePairLoss spatialLatticeWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg (spatialLatticeVector ab.1))))
    (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg (spatialLatticeVector ab.2))))

/-- The actual normalized low/high block has a convergent separated
Fourier expansion on its original support. The cutoff and coefficient
constant are fixed before the symbol or radial gap is chosen. -/
theorem exists_normalized_gap_box_series (S P : ℝ) (hS : 0 < S) (hSP : S < P) :
    ∃ (χ : BoxSpace → ℝ) (C : ℝ),
      ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ ball (0 : BoxSpace) P ∧
      (∀ z ∈ closedBall (0 : BoxSpace) S, χ z = 1) ∧ 0 ≤ C ∧
      ∀ (g : ℕ → BoxSpace → ℂ) (A : ℝ), 0 ≤ A →
      (∀ s, ContDiffOn ℝ 99 (g s) (ball (0 : BoxSpace) P)) →
      (∀ s n, n ≤ 40 → ∀ z ∈ ball (0 : BoxSpace) P,
        ‖iteratedFDeriv ℝ n (g s) z‖ ≤ A * radialGapDecay s) →
      ∀ s,
        let c (ab : FourierModePair) :=
          boxCubeFourierCoefficient P (modeIndex ab) (fun z => χ z • g s z)
        (∀ ab, ‖c ab‖ ≤ (C * A) * radialGapDecay s * modePairDecay ab) ∧
        ∀ z ∈ closedBall (0 : BoxSpace) S,
          Summable (fun ab => ‖c ab * separatedBoxMode P ab z‖) ∧
          HasSum (fun ab => c ab * separatedBoxMode P ab z) (g s z) := by
  let R := (S + P) / 2
  have hSR : S < R := by dsimp [R]; linarith
  have hRP : R < P := by dsimp [R]; linarith
  let bump : ContDiffBump (0 : BoxSpace) := ⟨S, R, hS, hSR⟩
  let χ : BoxSpace → ℝ := bump
  have hP : 0 < P := hS.trans hSP
  have hχ : ContDiff ℝ ∞ χ := bump.contDiff
  have hχSup : tsupport χ ⊆ closedBall (0 : BoxSpace) R := by rw [bump.tsupport_eq]
  have hχBall := hχSup.trans (closedBall_subset_ball hRP)
  have hOne : ∀ z ∈ closedBall (0 : BoxSpace) S, χ z = 1 :=
    fun _ hz => bump.one_of_mem_closedBall hz
  obtain ⟨K, hK, bχ⟩ := cutoff_forty_jets χ hχ P
  let C := boxDecayConstant P * ((2 : ℝ)^40 * K)
  have hC : 0 ≤ C := by dsimp [C, boxDecayConstant]; positivity
  refine ⟨χ, C, hχ, hχBall, hOne, hC, ?_⟩
  intro g A hA hg bg s c
  let f (z : BoxSpace) := χ z • g s z
  let M := A * radialGapDecay s
  have hM : 0 ≤ M := by dsimp [M, radialGapDecay]; positivity
  obtain ⟨hSmooth, hBound⟩ := cutoff_profile_forty_jets P χ hχ hχBall (g s)
    ((hg s).of_le (by norm_num)) K M hK hM bχ (bg s)
  have hs : tsupport f ⊆ closedBall (0 : BoxSpace) R :=
    (tsupport_smul_subset_left _ _).trans hχSup
  have hCompact : HasCompactSupport f := (isCompact_closedBall (0 : BoxSpace) R).of_isClosed_subset
    isClosed_closure hs
  have hBox : tsupport f ⊆ boxFourierCube P :=
    hs.trans (closed_ball_subset_box_fourier_cube R P hRP.le)
  have hDecay (ab : FourierModePair) : ‖c ab‖ ≤ (C * A) * radialGapDecay s * modePairDecay ab := by
    have h := joint_cube_coefficient_pair_decay P hP f hSmooth hCompact hBox _ (by positivity)
      (fun n hn z _ => hBound n hn z) ab
    convert h using 1
    dsimp [C, M]
    ring
  have hWeighted := (weighted_fourier_modes_at_gap c (C * A) (by positivity) s hDecay).1
  have hNorm : Summable (fun ab => ‖c ab‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ab => by simpa only [weightedModeCoefficient, mul_one] using
        mul_le_mul_of_nonneg_left (one_le_modePairLoss ab) (norm_nonneg (c ab))) hWeighted
  have hNormCube : Summable ((fun k => ‖boxCubeFourierCoefficient P k f‖) ∘ modeIndex) := hNorm
  have hCoeff : Summable (fun k => boxCubeFourierCoefficient P k f) :=
    (modeIndex.summable_iff.mp hNormCube).of_norm
  refine ⟨hDecay, fun z hz => ?_⟩
  have hzBox := closed_ball_subset_box_fourier_cube S P hSP.le hz
  have hSum := modeIndex.hasSum_iff.mpr
    (hasSum_box_cube_fourier_series P R hP hRP f hSmooth.continuous hs hCoeff z hzBox)
  have hf : f z = g s z := by simp [f, hOne z hz]
  rw [hf] at hSum
  refine ⟨?_, hSum.congr_fun ?_⟩
  · simpa only [norm_mul, norm_separatedBoxMode, mul_one] using hNorm
  · intro ab
    exact congrArg (fun w => c ab * w) (box_phase_exp_eq_separated P ab z).symm

end Burnett.A05.BoxFourier
