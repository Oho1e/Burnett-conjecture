import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeJointReduction
import Burnett.Analysis.TransportWard.Weyl.Amplitude.DyadicWeylCompleteSymbol
import Burnett.Analysis.TransportWard.Weyl.Amplitude.GeneralWeylFiniteCutoff
import Burnett.Analysis.TransportWard.Weyl.ProperLeftAction

/-! The exact A01 left action of the compact Weyl test, with the same two
physical cutoffs and the same full fixed-infrared symbol. -/

set_option autoImplicit false
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.CarlesonEmbedding (ProperKernelRelation firstOrderKernelRelation)
open scoped ContDiff FourierTransform Topology

open private dyadic_weyl_cutoff_smooth dyadic_weyl_cutoff_supported dyadic_weyl_cutoff_norm_le_one
  from Burnett.Analysis.TransportWard.Weyl.Amplitude.DyadicWeylCompleteSymbol

/-- The genuine compact Weyl amplitude. `β` is the full radian symbol,
with its one fixed infrared regularization already included. -/
def windowedWeylAmplitude (θ : E → ℝ) (β : E → E → ℂ) (x y ξ : E) : ℂ :=
  (θ x : ℂ) * (θ y : ℂ) * β ((1 / 2 : ℝ) • (x + y)) ξ

theorem windowedWeylAmplitude_diagonal (θ : E → ℝ) (β : E → E → ℂ) (x ξ : E) :
    windowedWeylAmplitude θ β x x ξ = (θ x : ℂ)^2 * β x ξ := by
  have h : (1 / 2 : ℝ) • (x + x) = x := by
    rw [← two_smul ℝ x, smul_smul]
    norm_num
  simp only [windowedWeylAmplitude, pow_two, h]

/-- The real radial frequency cutoff in A01, regarded as a Schwartz
function for the original A03 physical limit. -/
def windowedWeylDyadicCutoff (n : ℕ) : SchwartzMap E ℂ :=
  generalWeylCutoffProfile (dyadicWeylCutoff n) (dyadic_weyl_cutoff_smooth n)
    (dyadic_weyl_cutoff_supported n) 1 contDiff_const

theorem windowedWeylDyadicCutoff_apply (n : ℕ) (ξ : E) :
    windowedWeylDyadicCutoff n ξ = (dyadicWeylCutoff n ξ : ℂ) := by
  simp [windowedWeylDyadicCutoff, general_weyl_cutoff_profile_apply]

private theorem windowedWeylDyadicCutoff_bound (n : ℕ) (ξ : E) :
    ‖windowedWeylDyadicCutoff n ξ‖ ≤ 1 := by
  rw [windowedWeylDyadicCutoff_apply, Complex.norm_real]
  exact dyadic_weyl_cutoff_norm_le_one n ξ

private theorem windowedWeylDyadicCutoff_limit (ξ : E) :
    Tendsto (fun n => windowedWeylDyadicCutoff n ξ) atTop (𝓝 1) := by
  have h : (fun n => windowedWeylDyadicCutoff n ξ) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [dyadic_weyl_cutoff_eventually_one ξ] with n hn
    rw [windowedWeylDyadicCutoff_apply, hn, Complex.ofReal_one]
  exact tendsto_const_nhds.congr' h.symm

private theorem radianLeftQuantization_eq_firstOrderAction (b : E → E → ℂ)
    (u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization b u x = firstOrderAction (normalizedWeylSymbol b) u x := by
  simp only [radianLeftQuantization, firstOrderAction, Real.fourierIntegralInv_eq', normalizedWeylSymbol,
    Burnett.Microlocal.Overlap.baseFourierPhase, smul_eq_mul, mul_assoc]

/-- The genuine A03 reduced symbol, before the change to cycles. -/
def windowedWeylLeftRadianSymbol (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R) : E → E → ℂ :=
  radianAmplitudeReduced (radianSchwartzAmplitudeProfile
    (compactRadianTwoPointSlice (windowedWeylAmplitude θ β) R R h))

/-- One conversion from radians to the Fourier convention of A01. -/
def windowedWeylLeftSymbol (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R) : E → E → ℂ :=
  normalizedWeylSymbol (windowedWeylLeftRadianSymbol θ β R h)

/-- The exact physical cutoff limit equals the same left action on every
Schwartz input, under the ordinary compact amplitude hypotheses. -/
theorem windowedWeyl_dyadic_tendsto_leftAction (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => radianTwoPointCutoffAction (windowedWeylAmplitude θ β)
      (windowedWeylDyadicCutoff n) u x) atTop (𝓝 (firstOrderAction (windowedWeylLeftSymbol θ β R h) u x)) := by
  rw [windowedWeylLeftSymbol, ← radianLeftQuantization_eq_firstOrderAction]
  exact compact_radian_two_point_amplitude_cutoff_tendsto_left _ R R h _
    windowedWeylDyadicCutoff_bound windowedWeylDyadicCutoff_limit u x

/-- This is the remainder of the exact left action, taken relative to
the diagonal of the same doubly localized midpoint amplitude. -/
theorem windowedWeyl_leftRadian_remainder_order_zero (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hs : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β)) :
    RadianOrderZeroSymbolSeminorms
      (fun x ξ => windowedWeylLeftRadianSymbol θ β R h x ξ - (θ x : ℂ)^2 * β x ξ) := by
  simpa only [windowedWeylLeftRadianSymbol, windowedWeylAmplitude_diagonal] using
    compact_radian_two_point_left_diagonal_remainder_order_zero _ R R
      (compact_radian_scaled_order_one_of_directional _ R R h hs)

theorem windowedWeyl_leftAction_eq_zero_of_cutoffs (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (u : SchwartzMap E ℂ) (x : E) (hZero : θ x = 0 ∨ ∀ y, (θ y : ℂ) * u y = 0) :
    firstOrderAction (windowedWeylLeftSymbol θ β R h) u x = 0 := by
  have hRow (ξ : E) : (fun y => patchFourierPhase (-ξ) y *
      windowedWeylAmplitude θ β x y (tau • ξ) * u y) = fun _ => 0 := by
    funext y
    rcases hZero with ho | hi
    · simp [windowedWeylAmplitude, ho]
    · have he : patchFourierPhase (-ξ) y * windowedWeylAmplitude θ β x y (tau • ξ) * u y =
          (patchFourierPhase (-ξ) y * (θ x : ℂ) * β ((1 / 2 : ℝ) • (x+y)) (tau • ξ)) *
            ((θ y : ℂ) * u y) := by
        unfold windowedWeylAmplitude
        ring
      rw [he, hi y, mul_zero]
  have hf (n : ℕ) : radianTwoPointCutoffAction (windowedWeylAmplitude θ β)
      (windowedWeylDyadicCutoff n) u x = 0 := by
    unfold radianTwoPointCutoffAction
    simp [hRow]
  have hz : Tendsto (fun n => radianTwoPointCutoffAction (windowedWeylAmplitude θ β)
      (windowedWeylDyadicCutoff n) u x) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hf n).symm)
  exact tendsto_nhds_unique (windowedWeyl_dyadic_tendsto_leftAction θ β R h u x) hz

/-- With the order-one estimates on this same left symbol, genuine
properness of the A01 kernel is a consequence of the physical cutoffs. -/
theorem windowedWeyl_leftSymbol_proper (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R) (hc : HasCompactSupport θ)
    (ho : FrequencyOrderOne (windowedWeylLeftSymbol θ β R h))
    (hs : Continuous (uncurry (windowedWeylLeftSymbol θ β R h))) :
    ProperKernelRelation (firstOrderKernelRelation (windowedWeylLeftSymbol θ β R h)) := by
  refine proper_firstOrderKernelRelation_of_compact_cutoff_action ho hs hc hc ?_ ?_
  · intro u _ x hx
    exact windowedWeyl_leftAction_eq_zero_of_cutoffs θ β R h u x
      (Or.inl (image_eq_zero_of_notMem_tsupport hx))
  · intro u _ hup x
    apply windowedWeyl_leftAction_eq_zero_of_cutoffs θ β R h u x
    right
    intro y
    by_cases hy : y ∈ tsupport θ
    · have hu : u y = 0 := image_eq_zero_of_notMem_tsupport (fun hp => hup hp hy)
      rw [hu, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

end Burnett.V03
