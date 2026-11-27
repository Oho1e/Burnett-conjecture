import Burnett.Analysis.TransportWard.Weyl.PatchFourierPhase
import Burnett.Analysis.PrincipalEnergy.Quantization.FiniteFirstOrderAction
import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyKernel

set_option autoImplicit false
set_option maxHeartbeats 3100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Analysis.FirstOrderDyadic
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Microlocal.AngularDyadicKernel
  (radialCore radialCore_eq_zero radialCore_contDiff radialCore_eq_one radialCore_nonneg radialCore_le_one dyadicScale)
open scoped ContDiff FourierTransform ENNReal BigOperators Topology

/-- The A01 symbols are evaluated in mathlib frequency, with the original
radian phase of the A03 Weyl symbol retained. -/
def normalizedWeylSymbol (β : E → E → ℂ) (x ξ : E) : ℂ := β x (tau • ξ)

/-- The actual outer radialCore of the A01 finite low-plus-bands sum.
The fixed infrared regularization of the test is already in its symbol. -/
def dyadicWeylCutoff (N : ℕ) (ξ : E) : ℝ :=
  radialCore ((dyadicScale N)⁻¹ • ξ)

/-- Complete finite A01 cutoff of the same symbol, with no frequency
homogenization of either the principal or the order-zero part. -/
def dyadicWeylFiniteSymbol (β : E → E → ℂ) (N : ℕ) (x ξ : E) : ℂ :=
  firstOrderLowSymbol (normalizedWeylSymbol β) x ξ +
    firstOrderFiniteSymbol (normalizedWeylSymbol β) x N ξ

/-- The actual low term and the actual high annuli telescope to one
multiplication of the original normalized symbol. -/
theorem dyadic_weyl_finite_symbol_eq_cutoff (β : E → E → ℂ) (N : ℕ) (x ξ : E) :
    dyadicWeylFiniteSymbol β N x ξ = (dyadicWeylCutoff N ξ : ℂ) * β x (tau • ξ) := by
  unfold dyadicWeylFiniteSymbol
  rw [firstOrderFiniteSymbol_telescope]
  simp only [firstOrderLowSymbol, normalizedWeylSymbol, dyadicWeylCutoff, Complex.ofReal_sub]
  ring

theorem dyadic_weyl_cutoff_eventually_one (ξ : E) :
    (fun N => dyadicWeylCutoff N ξ) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => dyadicScale N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  filter_upwards [ht.eventually (eventually_ge_atTop ‖ξ‖)] with N hN
  have hNpos : 0 < dyadicScale N := by unfold dyadicScale; positivity
  apply radialCore_eq_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hNpos.le), ← div_eq_inv_mul]
  exact (div_le_one hNpos).2 hN

private theorem a01_radial_cutoff_frequency_integrable (a : E → ℂ) (ha : Continuous a) (s : ℝ) (hs : 0 < s) :
    Integrable (fun ξ => (radialCore (s⁻¹ • ξ) : ℂ) * a ξ) volume := by
  have h : Continuous (fun ξ : E => (radialCore (s⁻¹ • ξ) : ℂ) * a ξ) :=
    (Complex.continuous_ofReal.comp
      (radialCore_contDiff.continuous.comp (continuous_const.smul continuous_id))).mul ha
  apply h.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2*s))
  intro ξ hξ
  by_contra! outside
  have sz : 2*s < ‖ξ‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using outside
  have far : 2 ≤ ‖s⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ hs).mpr sz.le
  exact hξ (by simp only [radialCore_eq_zero _ far, Complex.ofReal_zero, zero_mul])

private theorem inverse_fourier_add_frequency_integrable (F G : E → ℂ)
    (hF : Integrable F volume) (hG : Integrable G volume) (z : E) :
    (𝓕⁻ (F+G)) z = (𝓕⁻ F) z + (𝓕⁻ G) z := by
  let p (ξ : E) := patchFourierPhase ξ z
  let arg (ξ : E) : E × E := (ξ,z)
  have ac : Continuous arg := continuous_id.prodMk continuous_const
  have pc : Continuous p := by
    change Continuous ((fun q : E × E => patchFourierPhase q.1 q.2) ∘ arg)
    exact patch_fourier_phase_continuous.comp ac
  have bounded : ∃ C : ℝ, ∀ ξ, ‖p ξ‖ ≤ C := ⟨1,fun ξ => (patch_fourier_phase_norm ξ z).le⟩
  simp only [Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, p ξ*(F ξ+G ξ)) = (∫ ξ, p ξ*F ξ) + (∫ ξ, p ξ*G ξ)
  simp_rw [mul_add]
  exact integral_add (hF.bdd_mul pc.aestronglyMeasurable bounded) (hG.bdd_mul pc.aestronglyMeasurable bounded)

/-- At this finite truncation the two-point kernel is precisely the low
A01 kernel plus the finite sum of its actual dyadic band kernels. -/
theorem dyadic_weyl_finite_inverse_eq_actual_bands (β : E → E → ℂ) (N : ℕ) (x z : E)
    (h : Continuous (normalizedWeylSymbol β x)) :
    (𝓕⁻ (dyadicWeylFiniteSymbol β N x)) z =
      firstOrderLowKernel (normalizedWeylSymbol β) x z +
      ∑ j ∈ Finset.range N, firstOrderAnnularKernel (normalizedWeylSymbol β) x j z := by
  let a := normalizedWeylSymbol β
  have lo : Integrable (firstOrderLowSymbol a x) volume := by
    simpa only [firstOrderLowSymbol, inv_one, one_smul] using a01_radial_cutoff_frequency_integrable (a x) h 1 zero_lt_one
  have hi : Integrable (firstOrderFiniteSymbol a x N) volume := by
    have hscale : 0 < dyadicScale N := by unfold dyadicScale; positivity
    have outer := a01_radial_cutoff_frequency_integrable (a x) h (dyadicScale N) hscale
    have eq : firstOrderFiniteSymbol a x N =
        (fun ξ => (radialCore ((dyadicScale N)⁻¹ • ξ) : ℂ)*a x ξ) - firstOrderLowSymbol a x := by
      funext ξ
      rw [firstOrderFiniteSymbol_telescope]
      simp only [Complex.ofReal_sub, Pi.sub_apply, firstOrderLowSymbol]
      ring
    rw [eq]
    exact outer.sub lo
  change (𝓕⁻ (firstOrderLowSymbol a x + firstOrderFiniteSymbol a x N)) z = _
  rw [inverse_fourier_add_frequency_integrable _ _ lo hi,
    inverseFourier_firstOrderFiniteSymbol a x h N z]
  rfl

/-- The literal midpoint integral with the actual A01 dyadic exhaustion. -/
def dyadicWeylMidpointTruncation (β : E → E → ℂ) (N : ℕ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ y : E, (∫ ξ : E, patchFourierPhase ξ (x-y) *
    (dyadicWeylCutoff N ξ : ℂ)*β ((1/2 : ℝ) • (x+y)) (tau • ξ)) * u y

theorem dyadic_weyl_midpoint_truncation_eq_actual_bands (β : E → E → ℂ) (N : ℕ)
    (h : ∀ x, Continuous (normalizedWeylSymbol β x)) (u : SchwartzMap E ℂ) (x : E) :
    dyadicWeylMidpointTruncation β N u x =
      ∫ y : E, (firstOrderLowKernel (normalizedWeylSymbol β) ((1/2 : ℝ) • (x+y)) (x-y) +
        ∑ j ∈ Finset.range N,
          firstOrderAnnularKernel (normalizedWeylSymbol β) ((1/2 : ℝ) • (x+y)) j (x-y)) * u y := by
  unfold dyadicWeylMidpointTruncation
  apply integral_congr_ae
  filter_upwards with y
  rw [← dyadic_weyl_finite_inverse_eq_actual_bands β N _ _ (h _)]
  congr 1
  simp only [Real.fourierIntegralInv_eq', dyadic_weyl_finite_symbol_eq_cutoff, smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by simp only [Burnett.Microlocal.Overlap.baseFourierPhase, mul_assoc]

end Burnett.A03
