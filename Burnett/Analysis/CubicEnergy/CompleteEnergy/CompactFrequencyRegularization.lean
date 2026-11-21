import Burnett.Analysis.CubicEnergy.CompleteEnergy.InfraredCubicContinuity

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open Metric Set Filter Burnett.RicciSymbol
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
/-- A smooth real replacement that agrees with b outside a fixed ball has the
exact cutoff-plus-addition representation used by the regularized estimate. -/
theorem compact_frequency_regularization_representation (cut : SchwartzMap E ℂ)
    (hzero : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (Rcut : ℝ) (hc : ∀ ζ, Rcut < ‖ζ‖ → fixedRadianProfile cut ζ = 0)
    (b r : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hr : ContDiff ℝ ∞ r)
    (Rreg : ℝ) (agree : ∀ ζ, Rreg < ‖ζ‖ → r ζ = b ζ) :
    ∃ a : SchwartzMap E ℂ, (∀ ξ, ((a ξ).re : ℂ) = a ξ) ∧
      HasCompactSupport (a : E → ℂ) ∧ r = fixedInfraredSymbol cut a b := by
  let S := fixedInfraredSymbol cut (0 : SchwartzMap E ℂ) b
  let δ := r - S
  have hS : ContDiff ℝ ∞ S :=
    fixedInfraredSymbol_smooth cut 0 b hb hzero
  have hd : ContDiff ℝ ∞ δ := hr.sub hS
  let R := max Rcut Rreg
  have support : Function.support δ ⊆ closedBall (0 : E) R := by
    intro ζ hζ
    by_contra hout
    have out : R < ‖ζ‖ := by
      apply lt_of_not_ge
      simpa only [mem_closedBall, dist_zero_right] using hout
    have hcut := hc ζ ((le_max_left Rcut Rreg).trans_lt out)
    have hreg := agree ζ ((le_max_right Rcut Rreg).trans_lt out)
    have hA : fixedRadianProfile (0 : SchwartzMap E ℂ) ζ = 0 := by simp [fixedRadianProfile]
    have base : S ζ = b ζ := fixedInfraredSymbol_outside cut 0 b ζ hcut hA
    exact hζ (sub_eq_zero.mpr (hreg.trans base.symm))
  have compactδ : HasCompactSupport δ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R) support
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have compactScaled : HasCompactSupport (fun ξ : E => δ (tau • ξ)) :=
    compactδ.comp_homeomorph (Homeomorph.smulOfNeZero tau hτ.ne')
  let A (ξ : E) : ℂ := (δ (tau • ξ) : ℂ)
  have compactA : HasCompactSupport A :=
    compactScaled.comp_left (show Complex.ofReal (0 : ℝ) = 0 by simp)
  have smoothA : ContDiff ℝ ∞ A :=
    Complex.ofRealCLM.contDiff.comp (hd.comp (contDiff_const.smul contDiff_id))
  let a := compactA.toSchwartzMap smoothA
  refine ⟨a, fun ξ => ?_, compactA, ?_⟩
  · change (((δ (tau • ξ) : ℂ)).re : ℂ) = (δ (tau • ξ) : ℂ)
    rw [Complex.ofReal_re]
  · have profile (ζ : E) : fixedRadianProfile a ζ = δ ζ := by
      change (δ (tau • (tau⁻¹ • ζ)) : ℂ).re = δ ζ
      rw [Complex.ofReal_re, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    funext ζ
    change r ζ = (1 - fixedRadianProfile cut ζ) * b ζ + fixedRadianProfile a ζ
    rw [profile]
    simp only [δ, Pi.sub_apply, S, fixedInfraredSymbol, fixedRadianProfile, SchwartzMap.zero_apply,
      Complex.zero_re, add_zero]
    ring

/-- The actual W¹³ continuity therefore applies to every smooth real
frequency-local replacement, with the cutoff kept fixed throughout. -/
theorem compact_frequency_regularization_continuity {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ)
    (cut : SchwartzMap E ℂ) (cutReal : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hzero : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (Rcut : ℝ) (cutOutside : ∀ ζ, Rcut < ‖ζ‖ → fixedRadianProfile cut ζ = 0)
    (b r : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (hr : ContDiff ℝ ∞ r)
    (Rreg : ℝ) (agree : ∀ ζ, Rreg < ‖ζ‖ → r ζ = b ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : RealEnergyField J,
      |completeCubicEnergy c q r u - completeCubicEnergy c q r v| ≤
        C * euclideanFieldW13 (↑(u-v) : J → SchwartzMap E ℂ) *
          (euclideanFieldW13 (u : J → SchwartzMap E ℂ) + euclideanFieldW13 (v : J → SchwartzMap E ℂ))^2 := by
  obtain ⟨a, realA, _, rep⟩ :=
    compact_frequency_regularization_representation cut hzero Rcut cutOutside b r hb hr Rreg agree
  obtain ⟨D,hD,jet⟩ := compact_sphere_jet 16 b hb
  obtain ⟨K,hK,est⟩ := fixed_infrared_complete_continuity_euclidean c hc q cut a cutReal realA
  refine ⟨K*(D+1), mul_nonneg hK (by positivity), ?_⟩
  simpa only [rep] using est b hb hom D hD jet

end Burnett.A02.FrequencySplit
