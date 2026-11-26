import Burnett.Analysis.FrozenTransport.ActualV10Infrared

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric Burnett.P01 Burnett.C02 Burnett.V03
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open private physical_low from Burnett.Analysis.FrozenTransport.ActualV10Infrared

def actualFarAngularProfile (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ)
    (κ δ b i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g))
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) (k j l : OrderedPair) (y : Joint × E) : ℂ :=
  actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l (y.2, y.1)

private def angularOrder (y : Joint × E) : FarProfilePoint := (y.2, y.1)

def farAngularDomain : Set (Joint × E) := angularOrder ⁻¹' cyclicExtensionDomain

theorem farAngularDomain_open : IsOpen farAngularDomain :=
  isOpen_cyclicExtensionDomain.preimage (continuous_snd.prodMk continuous_fst)

theorem farAngularDomain_contains_correction_window :
    (closedBall (0 : E) (1 / 4) ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1 ⊆ farAngularDomain := by
  intro y hy
  have hω := mem_sphere_zero_iff_norm.mp hy.2
  have hz := mem_closedBall_zero_iff.mp hy.1.1
  have hh := mem_sphere_zero_iff_norm.mp hy.1.2
  refine ⟨?_, ?_⟩
  · change y.2 ≠ 0
    intro he
    simp [he] at hω
  · change ‖y.1.1‖ < ‖y.1.2‖
    linarith

/-- The actual thin-screen quotient is jointly smooth in the independent
variables of the first-order angular expansion. -/
theorem actualFarAngularProfile_contDiffOn (g : Mat) (a : Vec → ℝ)
    (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec)) (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ : ℝ) (hκ : 0 < κ) (δ b i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g))
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) (k j l : OrderedPair) :
    ContDiffOn ℝ ∞ (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l) farAngularDomain :=
  (actualThinFarCubicCorrection_contDiffOn g ha hϑ hκ δ b i o hm hη inn out k j l).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hy => hy)

/-- The squared-ratio cutoff used for the angular series leaves the exact
physical quotient unchanged wherever the original low weight is active. -/
theorem actualThinFar_ratio_guard_inert (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ)
    (cut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) (κ : ℝ) (hκ : 0 < κ) (hs : κ < 1 / 16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (p q : Vec) :
    let R := ‖q‖⁻¹ • p
    let B := (‖q‖ : ℂ) * actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
      (physicalFarProfilePoint p q)
    ((1 - gaugeProjectionInfrared (64 * ‖R‖ ^ 2) : ℝ) : ℂ) * B = B := by
  intro R B
  by_cases hq : q = 0
  · subst q
    simp [B]
  by_cases hL : lowSlotWeight ϑ κ p q (-(p + q)) = 0
  · have hz : ϑ (farLowArgument κ (physicalFarProfilePoint p q)) = 0 := by
      rw [physical_low hq hκ]
      exact hL
    have hz' : B = 0 := by
      simp only [B, actualThinFarCubicCorrection, farPhysicalCubicCorrection, cutoffGuardedFarProfile,
        farCutoffExtension, hz, zero_mul, Complex.ofReal_zero, mul_zero]
    simp [hz']
  have hlow := lowSlotWeight_nonzero_small cut hκ hs (add_neg_cancel (p + q)) hq hL
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hR : ‖R‖ < 1 / 8 := by
    have hn : ‖R‖ = ‖p‖ / ‖q‖ := by
      simp [R, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hqn.le), div_eq_inv_mul]
    rw [hn, div_lt_iff₀ hqn]
    nlinarith [mul_lt_mul_of_pos_right hs hqn]
  have hsize : 64 * ‖R‖ ^ 2 ≤ 1 := by
    nlinarith [mul_self_lt_mul_self (norm_nonneg R) hR]
  simp only [gaugeProjectionInfrared_zero hsize, sub_zero, Complex.ofReal_one, one_mul]

end Burnett.V10.OriginalGaugeCompatibility
