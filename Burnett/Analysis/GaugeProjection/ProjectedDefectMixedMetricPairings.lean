import Burnett.Analysis.GaugeProjection.ProjectedDefectMixedPairings
import Burnett.Analysis.GaugeProjection.ProjectedDefectOriginalGradient
import Burnett.Analysis.GaugeProjection.ProjectedCutoffDerivativeWeakZero

set_option autoImplicit false
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.P01

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Topology Matrix NNReal ComplexConjugate

/-- Given the pairing witness for the weighted original jets, the two
independently chosen derivatives of the same projected cutoff fluctuation
have the projected amplitude covariance with both frequency factors. -/
theorem projectedLocalizedMetric_weighted_mixedPairing_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p ξ : X → E) (A : X → Matrix OrderedPair OrderedPair ℂ)
    (hp : Measurable p) (hξ : Measurable ξ)
    (a χ : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (ha0 : DegreeZero (a : E → ℂ))
    (hχReal : ∀ y, conj (χ y) = χ y)
    (hχm : Measurable (χ : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (U : Set E) (hU : IsOpen U)
    (g : ℕ → E → Tensor2) (g₀ : E → Tensor2)
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport η))
    (B : ℝ≥0) (hDeriv : ∀ n i j y, y ∈ tsupport η →
      ‖fderiv ℝ (fun v => g n v i j - g₀ v i j) y‖ ≤ (B : ℝ))
    (d : D) (ρ : BoundedSymbol E) (hρ : ∀ y, ρ y = ((d : E → ℝ) y : ℂ))
    (W : Index → ℕ → OrderedPair → ComplexL2 E)
    (hW : ∀ s n k, (W s n k : E → ℂ) =ᵐ[volume] fun y =>
      (((d : E → ℝ) y * η y *
        (coordinateJet (g n) y s k.1 k.2 - coordinateJet g₀ y s k.1 k.2) : ℝ) : ℂ))
    (C₀ : ℝ) (hWBound : ∀ s n k, ‖W s n k‖ ≤ C₀)
    (α β : Index)
    (hA : ∀ k l, Integrable (fun v => ((ξ v α : ℂ) * (ξ v β : ℂ)) * A v k l) μ)
    (hPair : ∀ (k l : OrderedPair) (b : BoundedSymbol E),
      ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E) → DegreeZero (b : E → ℂ) →
      Tendsto (fun n => inner ℂ (W α n k) (symbolCLM χ (fourierMultiplier b (W β n l)))) atTop
        (𝓝 (∫ v, χ (p v) * b (ξ v) * ((ξ v α : ℂ) * (ξ v β : ℂ)) * A v l k ∂μ)))
    (i j : OrderedPair) :
    let z n := localizedMetricSchwartz (g n) g₀ η hη hηc (hg n) hg₀
    let w s n (k : OrderedPair) := symbolCLM ρ
      ((coordinateDerivative s (projectionFullSchwartz (z n) k.1 k.2)).toLp 2 volume)
    Tendsto (fun n => inner ℂ (w α n i) (symbolCLM χ (fourierMultiplier a (w β n j)))) atTop
      (𝓝 (∫ v, χ (p v) * a (ξ v) * ((ξ v α : ℂ) * (ξ v β : ℂ)) *
        (principalGaugeProjectionMatrix (ξ v) * A v * (principalGaugeProjectionMatrix (ξ v))ᴴ) j i ∂μ)) := by
  intro z w
  let F (s : Index) (n : ℕ) (k : OrderedPair) (y : E) :=
    (coordinateDerivative s (z n k.1 k.2) y).re
  obtain ⟨θ, C, _, _, _, hCut, hf, hLp, hBound, hWeak⟩ :=
    exists_localizedMetricSchwartz_coordinateDerivative_defect_inputs U hU g g₀ η hη hηc
      hηU hg hg₀ hConv B hDeriv
  have hRep (s : Index) (n : ℕ) (k : OrderedPair) :
      sourceSchwartz (hf n s k.1 k.2) θ (hCut n s k.1 k.2) =
        coordinateDerivative s (z n k.1 k.2) := by
    ext y
    change ((F s n k y : ℝ) : ℂ) = coordinateDerivative s (z n k.1 k.2) y
    have hd := localizedMetricSchwartz_coordinateDerivative_real
      (g n) g₀ η hη hηc (hg n) hg₀ k.1 k.2 s y
    change coordinateDerivative s (z n k.1 k.2) y = _ at hd
    simp only [F, hd, Complex.ofReal_re]
  have hErr (s : Index) (k : OrderedPair) :
      Tendsto (fun n => symbolCLM ρ ((sourceSchwartz (hf n s k.1 k.2) θ
        (hCut n s k.1 k.2)).toLp 2 volume) - W s n k) atTop (𝓝 0) := by
    simp only [hRep]
    exact localizedMetric_weighted_derivative_sub_original_tendsto_zero
      g g₀ η hη hηc hg hg₀ hConv d ρ hρ k.1 k.2 s (fun n => W s n k) (fun n => hW s n k)
  let N (v : X) := ((ξ v α : ℂ) * (ξ v β : ℂ)) • A v
  have hN (k l : OrderedPair) : Integrable (fun v => N v k l) μ := by
    simpa only [N, Matrix.smul_apply, smul_eq_mul] using hA k l
  have hPairN (k l : OrderedPair) (b : BoundedSymbol E)
      (hb : ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E)) (hb0 : DegreeZero (b : E → ℂ)) :
      Tendsto (fun n => inner ℂ (W α n k) (symbolCLM χ (fourierMultiplier b (W β n l)))) atTop
        (𝓝 (∫ v, χ (p v) * b (ξ v) * N v l k ∂μ)) := by
    simpa only [N, Matrix.smul_apply, smul_eq_mul, mul_assoc] using hPair k l b hb hb0
  have ht := projectionFullSchwartz_weighted_mixed_defectPairing_tendsto μ p ξ N hp hξ hN
    a χ ha ha0 hχReal hχm hχ hχc d ρ hρ F
    (fun s n k => hf n s k.1 k.2) (fun s n k => hLp n s k.1 k.2) θ
    (fun s n k => hCut n s k.1 k.2) C (fun s n k => hBound n s k.1 k.2)
    (fun s k φ => hWeak s k.1 k.2 φ) W C₀ hWBound hErr α β hPairN i j
  have hProjD (s : Index) (n : ℕ) :
      projectionFullSchwartz (fun p q => coordinateDerivative s (z n p q)) =
        fun p q => coordinateDerivative s (projectionFullSchwartz (z n) p q) :=
    projectionFullSchwartz_coordinateDerivative s (z n)
  simpa only [w, hRep, hProjD, N, mul_smul_comm, smul_mul_assoc,
    Matrix.smul_apply, smul_eq_mul, mul_assoc] using ht

end Burnett.P01
