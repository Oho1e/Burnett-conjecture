import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Burnett.Analysis.Microlocal.SeparableSquareOperators
import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

/-! Reflection of actual separated pairings for the real original jet. -/
set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.F05.OriginalCoordinateCurl (originalGradientSchwartz originalGradientSchwartz_apply)
open Burnett.F05.ChartVolumeBridge (chartVolumeWeightedCutoff chartVolumeWeightedCutoff_tsupport)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularDyadicKernel (E fourierMultiplier_schwartz_eq_inverse_mul_ae)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SeparablePositive (separableOperator conjugateSymbol conjugateSymbol_apply)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold

/-- Complex conjugation of a frequency multiplier reverses the input frequency. -/
def conjugateReflectedAngularSymbol (m : BoundedSymbol E) : BoundedSymbol E where
  toFun := fun ξ => conj (m (-ξ))
  measurable := Complex.continuous_conj.comp_aestronglyMeasurable
    (m.measurable.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure E)))
  bound := m.bound
  bound_nonneg := m.bound_nonneg
  norm_le ξ := by simpa only [Complex.norm_conj] using m.norm_le (-ξ)

private theorem inverseFourier_reflect_conj (g : E → ℂ) (x : E) :
    𝓕⁻ (fun ξ => conj (g (-ξ))) x = conj (𝓕⁻ g x) := by
  let N : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  rw [Real.fourierIntegralInv_eq_fourierIntegral_neg]
  change 𝓕 ((fun ξ => conj (g ξ)) ∘ N) (-x) = _
  rw [Real.fourierIntegral_comp_linearIsometry]
  have hN : N (-x) = x := by simp [N]
  rw [hN]
  exact fourier_conj_eq_conj_inverse g x

private theorem fourier_neg_of_real (f : E → ℂ) (hr : ∀ x, conj (f x) = f x) (ξ : E) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  have h := fourier_conj_eq_conj_inverse f (-ξ)
  simpa only [hr, Real.fourierIntegralInv_eq_fourierIntegral_neg, neg_neg] using h

private theorem inner_separableOperator_schwartz_integral (a m : BoundedSymbol E)
    (f v : SchwartzMap E ℂ) :
    inner ℂ (f.toLp 2 volume) (separableOperator a m (v.toLp 2 volume)) =
      ∫ x, conj (f x) * (a x * (𝓕⁻ (fun ξ => m ξ * (𝓕 (v : E → ℂ)) ξ)) x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume,
    symbolL2_ae a (fourierMultiplier m (v.toLp 2 volume)),
    fourierMultiplier_schwartz_eq_inverse_mul_ae m v] with x hf ha hm
  change inner ℂ ((f.toLp 2 volume : E → ℂ) x)
    ((symbolL2 a (fourierMultiplier m (v.toLp 2 volume))) x) = _
  rw [RCLike.inner_apply', hf, ha, hm]

/-- The same two real original inputs give the conjugate pairing after the
base weight is conjugated and the angular symbol is conjugated and reflected. -/
theorem conj_realSchwartz_separablePairing_eq_reflected (a m : BoundedSymbol E)
    (f v : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (hv : ∀ x, conj (v x) = v x) :
    conj (inner ℂ (f.toLp 2 volume) (separableOperator a m (v.toLp 2 volume))) =
      inner ℂ (f.toLp 2 volume)
        (separableOperator (conjugateSymbol a) (conjugateReflectedAngularSymbol m) (v.toLp 2 volume)) := by
  rw [inner_separableOperator_schwartz_integral, inner_separableOperator_schwartz_integral, ← integral_conj]
  let G (ξ : E) := m ξ * (𝓕 (v : E → ℂ)) ξ
  have hG : (fun ξ => conjugateReflectedAngularSymbol m ξ * (𝓕 (v : E → ℂ)) ξ) =
      (fun ξ => conj (G (-ξ))) := by
    funext ξ
    dsimp only [G]
    rw [show conjugateReflectedAngularSymbol m ξ = conj (m (-ξ)) from rfl, map_mul,
      fourier_neg_of_real (v : E → ℂ) hv ξ, starRingEnd_self_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change conj (conj (f x) * (a x * (𝓕⁻ G) x)) =
      conj (f x) * (conjugateSymbol a x *
        (𝓕⁻ (fun ξ => conjugateReflectedAngularSymbol m ξ * (𝓕 (v : E → ℂ)) ξ)) x)
    rw [hG, inverseFourier_reflect_conj G x]
    simp only [map_mul, hf, conjugateSymbol_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- This reflection applies directly to the original physical-volume half-density
coordinate gradients present in the chart measure representation. -/
theorem conj_originalVolume_separablePairing_eq_reflected
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (q : CompactChartInput M) (a m : BoundedSymbol E) (n : ℕ) (i j : JetSlot) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart) n
    conj (inner ℂ (w i) (separableOperator a m (w j))) =
      inner ℂ (w i) (separableOperator (conjugateSymbol a) (conjugateReflectedAngularSymbol m) (w j)) := by
  let hq := q.cutoff_support.trans q.ball_in_chart
  let ψ := chartVolumeWeightedCutoff B hB hn q.center q.cutoff hq
  let hψ := (chartVolumeWeightedCutoff_tsupport B hB hn q.center q.cutoff hq).trans hq
  let f (k : JetSlot) := originalGradientSchwartz B g hB hg q.center ψ hψ n k
  have hReal (k : JetSlot) (x : E) : conj (f k x) = f k x := by
    dsimp only [f]
    rw [originalGradientSchwartz_apply]
    exact Complex.conj_ofReal _
  exact conj_realSchwartz_separablePairing_eq_reflected a m (f i) (f j) (hReal i) (hReal j)

end Burnett.Microlocal.Overlap
