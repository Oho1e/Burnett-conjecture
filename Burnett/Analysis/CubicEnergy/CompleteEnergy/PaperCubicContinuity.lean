import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompactFrequencyRegularization
import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicEuclidean
import Burnett.Analysis.Fourier.FixedInfraredSchwartz
import Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 3500

noncomputable section

namespace Burnett.A02.FrequencySplit

open Filter Metric Burnett.RicciSymbol Burnett.Analysis.SignedFourierWindow
open Burnett.P01 (gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
  gaugeProjectionInfrared_zero gaugeProjectionInfrared_one)
open scoped ContDiff Topology

open private lowInfraredSchwartz from Burnett.Analysis.Fourier.FixedInfraredSchwartz

private def cubicInfraredReferenceCut : SchwartzMap E ℂ :=
  lowInfraredSchwartz gaugeProjectionInfrared gaugeProjectionInfrared_contDiff 1 2
    zero_lt_one (fun _ h => gaugeProjectionInfrared_zero h) (fun _ h => gaugeProjectionInfrared_one h)

private theorem cubicInfraredReferenceCut_real (ξ : E) :
    ((cubicInfraredReferenceCut ξ).re : ℂ) = cubicInfraredReferenceCut ξ := by
  change (((1 - gaugeProjectionInfrared (tau * ‖ξ‖) : ℝ) : ℂ).re : ℂ) =
    ((1 - gaugeProjectionInfrared (tau * ‖ξ‖) : ℝ) : ℂ)
  rw [Complex.ofReal_re]

private theorem cubicInfraredReferenceCut_profile (ζ : E) :
    fixedRadianProfile cubicInfraredReferenceCut ζ = 1 - gaugeProjectionInfrared ‖ζ‖ := by
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hnorm : tau * ‖tau⁻¹ • ζ‖ = ‖ζ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le), ← mul_assoc,
      mul_inv_cancel₀ hτ.ne', one_mul]
  change ((1 - gaugeProjectionInfrared (tau * ‖tau⁻¹ • ζ‖) : ℝ) : ℂ).re = _
  rw [Complex.ofReal_re, hnorm]

private theorem cubicInfraredReferenceCut_plateau :
    ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cubicInfraredReferenceCut ζ = 1 := by
  have h : (0 : E) ∈ {ζ : E | ‖ζ‖ < (1 : ℝ)} := by simp
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with ζ hζ
  have hsmall : ‖ζ‖ < (1 : ℝ) := hζ
  rw [cubicInfraredReferenceCut_profile, gaugeProjectionInfrared_zero hsmall.le, sub_zero]

private theorem cubicInfraredReferenceCut_outside (ζ : E) (hζ : 2 < ‖ζ‖) :
    fixedRadianProfile cubicInfraredReferenceCut ζ = 0 := by
  rw [cubicInfraredReferenceCut_profile, gaugeProjectionInfrared_one hζ.le, sub_self]

/-- Lemma 3.2 for the actual complete radian Fourier energy. The real
Schwartz class contains the compactly supported smooth fields of the paper.
The inhomogeneous assertion covers any smooth real modification supported
in a fixed bounded frequency region. -/
theorem paper_completeCubic_continuity {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a, d), (i, j)) l = c ((d, a), (j, i)) l)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ζ | ζ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ζ, b (t • ζ) = t * b ζ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u v : RealEnergyField J,
      |completeCubicEnergy c q b u - completeCubicEnergy c q b v| ≤
        C * euclideanFieldGradientL3 (↑(u - v) : J → SchwartzMap E ℂ) *
          (euclideanFieldGradientL3 (u : J → SchwartzMap E ℂ) +
            euclideanFieldGradientL3 (v : J → SchwartzMap E ℂ)) ^ 2) ∧
    (∀ r : E → ℝ, ContDiff ℝ ∞ r → (∃ R : ℝ, ∀ ζ, R < ‖ζ‖ → r ζ = b ζ) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : RealEnergyField J,
        |completeCubicEnergy c q r u - completeCubicEnergy c q r v| ≤
          C * euclideanFieldW13 (↑(u - v) : J → SchwartzMap E ℂ) *
            (euclideanFieldW13 (u : J → SchwartzMap E ℂ) +
              euclideanFieldW13 (v : J → SchwartzMap E ℂ)) ^ 2) := by
  refine ⟨complete_cubic_energy_difference_euclidean c hc q b hb hom, ?_⟩
  intro r hr hAgree
  obtain ⟨R, hR⟩ := hAgree
  exact compact_frequency_regularization_continuity c hc q
    cubicInfraredReferenceCut cubicInfraredReferenceCut_real cubicInfraredReferenceCut_plateau
    2 cubicInfraredReferenceCut_outside b r hb hom hr R hR

end Burnett.A02.FrequencySplit
