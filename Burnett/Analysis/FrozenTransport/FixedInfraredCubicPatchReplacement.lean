import Burnett.Analysis.CubicEnergy.CompleteEnergy.InfraredCubicContinuity

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.TransportPatches

open Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Index)
open Filter Metric
open scoped ContDiff Topology

/-- Replacement of the physical field in all three factors of the complete
fixed-infrared energy, with the same gauge field in the two inputs. The (L^3)
volume of the error and the other two factors multiply to the patch volume. -/
theorem exists_completeCubic_patch_replacement {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (u v G : ℕ → RealEnergyField J) (Ce Cp ell alpha mass : ℝ),
      0 ≤ Ce → 0 ≤ Cp → 0 ≤ ell → 0 ≤ mass →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        euclideanFieldW13 (↑(u n - v n) : J → SchwartzMap E ℂ) ≤
          Ce * ell ^ alpha * mass ^ (1 / 3 : ℝ) + ε) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        euclideanFieldW13 (↑(u n + G n) : J → SchwartzMap E ℂ) +
          euclideanFieldW13 (↑(v n + G n) : J → SchwartzMap E ℂ) ≤
          Cp * mass ^ (1 / 3 : ℝ) + ε) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        |completeCubicEnergy c q (fixedInfraredSymbol cut add b) (u n + G n) -
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) (v n + G n)| ≤
          (C * (D + 1) * Ce * Cp^2) * ell ^ alpha * mass + ε := by
  obtain ⟨C, hC, continuous⟩ := fixed_infrared_complete_continuity_euclidean c hc q cut add hcut hadd
  refine ⟨C, hC, ?_⟩
  intro b hb hom D hD jets u v G Ce Cp ell alpha mass hCe hCp hEll hMass hDiff hPair ε hε
  let W (f : RealEnergyField J) := euclideanFieldW13 (f : J → SchwartzMap E ℂ)
  let K := C * (D + 1)
  let m := mass ^ (1 / 3 : ℝ)
  let R := Ce * ell ^ alpha * m
  let B := Cp * m
  let F (t : ℝ) := K * (R + t) * (B + t)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hR : 0 ≤ R := by dsimp [R, m]; positivity
  have hB : 0 ≤ B := by dsimp [B, m]; positivity
  have hW (f : RealEnergyField J) : 0 ≤ W f := ENNReal.toReal_nonneg
  have hm : m * m^2 = mass := by
    dsimp [m]
    rw [pow_two, ← Real.rpow_add_of_nonneg hMass (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3), ← Real.rpow_add_of_nonneg hMass
        (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3)]
    rw [show (1 / 3 : ℝ) + (1 / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
  have hF0 : F 0 = (K * Ce * Cp^2) * ell ^ alpha * mass := by
    dsimp only [F, R, B]
    simp only [add_zero]
    rw [← hm]
    ring
  have hF : Continuous F := by fun_prop
  have hNear : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, F t < F 0 + ε :=
    (hF.continuousWithinAt : ContinuousWithinAt F (Set.Ioi 0) 0).eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  have ht : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hsmall, hpos⟩ := (hNear.and ht).exists
  filter_upwards [hDiff t hpos, hPair t hpos] with n hd hp
  have hCancel : u n + G n - (v n + G n) = u n - v n := add_sub_add_right_eq_sub _ _ _
  have hEnergy := continuous b hb hom D hD jets (u n + G n) (v n + G n)
  rw [hCancel] at hEnergy
  calc
    _ ≤ K * W (u n - v n) * (W (u n + G n) + W (v n + G n))^2 := hEnergy
    _ ≤ F t := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hd hK
      · exact pow_le_pow_left₀ (add_nonneg (hW _) (hW _)) hp 2
      · positivity
      · exact mul_nonneg hK (add_nonneg hR hpos.le)
    _ ≤ _ := by rw [← hF0]; exact hsmall.le

end Burnett.Analysis.TransportPatches
