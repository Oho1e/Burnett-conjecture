import Burnett.Analysis.GaugeProjection.ProjectedDefectMatrixPairing
import Burnett.Analysis.GaugeProjection.ProjectedDefectStablePairings

set_option autoImplicit false
set_option maxHeartbeats 8400000

noncomputable section

namespace Burnett.P01

open Matrix MeasureTheory Filter Set Burnett.Fourier
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff Matrix ComplexConjugate Topology

private theorem norm_realSchwartz_toLp
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (χ₀ : D)
    (hc : ∀ x, f x ≠ 0 → (χ₀ : E → ℝ) x = 1) (hLp : MemLp f 2 volume) :
    ‖(sourceSchwartz hf χ₀ hc).toLp 2 volume‖ = ‖hLp.toLp f‖ := by
  rw [SchwartzMap.toLp, Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  change eLpNorm (fun x => (f x : ℂ)) 2 volume = eLpNorm f 2 volume
  exact le_antisymm (eLpNorm_mono (fun x => (Complex.norm_real _).le))
    (eLpNorm_mono (fun x => (Complex.norm_real _).ge))

private theorem norm_projEntry_toLp_le (w : ProjectionSchwartzMatrix) (B : ℝ)
    (hB : ∀ a b, ‖(w a b).toLp 2 volume‖ ≤ B) (i j : Fin 4) :
    ‖(projectionFullSchwartz w i j).toLp 2 volume‖ ≤ ‖projectionFullL2‖ * B := by
  have hW : ‖projectionMatrixToL2 w‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hB 0 0))).2
    intro a
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hB 0 0))).2
    exact hB a
  let V := projectionMatrixToL2 (projectionFullSchwartz w)
  have hV : V = projectionFullL2 (projectionMatrixToL2 w) :=
    (projectionFullL2_eq_schwartz w).symm
  have hEntry : ‖V i j‖ ≤ ‖V‖ :=
    (norm_le_pi_norm (V i) j).trans (norm_le_pi_norm V i)
  calc
    _ ≤ ‖V‖ := hEntry
    _ = ‖projectionFullL2 (projectionMatrixToL2 w)‖ := by rw [hV]
    _ ≤ ‖projectionFullL2‖ * B :=
      (projectionFullL2.le_opNorm _).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg _))

/-- The same trace and angular covariance describe the actual weighted
projected derivative tests when the old F05 derivative input differs from
the weighted cutoff derivative by a strong L² error. -/
theorem projectionFullSchwartz_weighted_defectPairing_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (x : X → E) (ξ : X → E) (N : X → Matrix OrderedPair OrderedPair ℂ)
    (hx : Measurable x) (hξ : Measurable ξ) (hN : ∀ i j, Integrable (fun z => N z i j) μ)
    (a χ : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (ha0 : DegreeZero (a : E → ℂ))
    (hχReal : ∀ y, conj (χ y) = χ y) (hχm : Measurable (χ : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (d : D) (ρ : BoundedSymbol E) (hρ : ∀ y, ρ y = ((d : E → ℝ) y : ℂ))
    (f : ℕ → OrderedPair → E → ℝ) (hf : ∀ n k, ContDiff ℝ ∞ (f n k))
    (fLp : ∀ n k, MemLp (f n k) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ n k y, f n k y ≠ 0 → (χ₀ : E → ℝ) y = 1)
    (B : ℝ) (hB : ∀ n k, ‖(fLp n k).toLp (f n k)‖ ≤ B)
    (hWeak : ∀ k (φ : D), Tendsto (fun n => ∫ y, f n k y * (φ : E → ℝ) y) atTop (𝓝 0))
    (W : ℕ → OrderedPair → ComplexL2 E) (B₀ : ℝ) (hB₀ : ∀ n k, ‖W n k‖ ≤ B₀)
    (hErr : ∀ k, Tendsto (fun n => symbolCLM ρ
      ((sourceSchwartz (hf n k) χ₀ (hCut n k)).toLp 2 volume) - W n k) atTop (𝓝 0))
    (hPair : ∀ (k l : OrderedPair) (b : BoundedSymbol E), ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E) →
      DegreeZero (b : E → ℂ) →
      Tendsto (fun n => inner ℂ (W n k) (symbolCLM χ (fourierMultiplier b (W n l)))) atTop
        (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ))) (i j : OrderedPair) :
    let u := fun n p q => sourceSchwartz (hf n (p,q)) χ₀ (hCut n (p,q))
    let V := fun n (k : OrderedPair) =>
      symbolCLM ρ ((projectionFullSchwartz (u n) k.1 k.2).toLp 2 volume)
    Tendsto (fun n => inner ℂ (V n i) (symbolCLM χ (fourierMultiplier a (V n j)))) atTop
      (𝓝 (∫ z, χ (x z) * a (ξ z) *
        (principalGaugeProjectionMatrix (ξ z) * N z * (principalGaugeProjectionMatrix (ξ z))ᴴ) j i ∂μ)) := by
  intro u V
  let g (n : ℕ) (k : OrderedPair) (y : E) := (d : E → ℝ) y * f n k y
  have hg (n : ℕ) (k : OrderedPair) : ContDiff ℝ ∞ (g n k) := (test_smooth d).mul (hf n k)
  have hgCut (n : ℕ) (k : OrderedPair) (y : E) (h : g n k y ≠ 0) : (χ₀ : E → ℝ) y = 1 :=
    hCut n k y (fun hh => h (mul_eq_zero.mpr (Or.inr hh)))
  have gLp (n : ℕ) (k : OrderedPair) : MemLp (g n k) 2 volume := by
    apply (fLp n k).of_le_mul (c := ρ.bound) (hg n k).continuous.aestronglyMeasurable
    filter_upwards with y
    change ‖(d : E → ℝ) y * f n k y‖ ≤ _
    rw [norm_mul]
    have hd : ‖(d : E → ℝ) y‖ ≤ ρ.bound := by
      simpa only [hρ, Complex.norm_real] using ρ.norm_le y
    exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  let w (n : ℕ) (k : OrderedPair) := sourceSchwartz (hg n k) χ₀ (hgCut n k)
  let U (n : ℕ) (k : OrderedPair) := (w n k).toLp 2 volume
  have hEq (n : ℕ) (k : OrderedPair) :
      U n k = symbolCLM ρ ((sourceSchwartz (hf n k) χ₀ (hCut n k)).toLp 2 volume) := by
    let F := sourceSchwartz (hf n k) χ₀ (hCut n k)
    apply Lp.ext
    filter_upwards [(w n k).coeFn_toLp 2 volume, F.coeFn_toLp 2 volume,
      symbolL2_ae ρ (F.toLp 2 volume)] with y h₁ h₂ h₃
    change _ = symbolL2 ρ (F.toLp 2 volume) y
    rw [h₁, h₃, h₂, hρ]
    exact Complex.ofReal_mul _ _
  have hU (n : ℕ) (k : OrderedPair) :
      ‖U n k‖ ≤ ‖symbolCLM ρ‖ * B := by
    rw [hEq]
    apply ((symbolCLM ρ).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_realSchwartz_toLp (f n k) (hf n k) χ₀ (hCut n k) (fLp n k)).trans_le (hB n k)
  have hG (n : ℕ) (k : OrderedPair) :
      ‖(gLp n k).toLp (g n k)‖ ≤ ‖symbolCLM ρ‖ * B := by
    rw [← norm_realSchwartz_toLp (g n k) (hg n k) χ₀ (hgCut n k) (gLp n k)]
    exact hU n k
  have hWeakG (k : OrderedPair) :
      ∀ (φ : D), Tendsto (fun n => ∫ y, g n k y * (φ : E → ℝ) y) atTop (𝓝 0) := by
    intro φ
    let ψ : D := ⟨fun y => d.val y * φ.val y, (test_smooth d).mul (test_smooth φ),
      (test_compactSupport d).mul_right⟩
    convert hWeak k ψ using 1
    funext n
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      change d.val y * f n k y * φ.val y = f n k y * (d.val y * φ.val y)
      ring)
  have hM (k : OrderedPair) : Tendsto (fun n => U n k - W n k) atTop (𝓝 0) := by
    simp only [hEq]
    exact hErr k
  have hPairG (k l : OrderedPair) (b : BoundedSymbol E)
      (hb : ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E)) (hb0 : DegreeZero (b : E → ℂ)) :
      Tendsto (fun n => inner ℂ (U n k) (symbolCLM χ (fourierMultiplier b (U n l)))) atTop
        (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ)) := by
    have he := defectPairing_sub_tendsto_zero_of_strong_errors
      ((symbolCLM χ).comp (fourierMultiplier b))
      (fun n => W n k) (fun n => W n l) (fun n => U n k) (fun n => U n l)
      B₀ (‖symbolCLM ρ‖ * B) (fun n => hB₀ n k) (fun n => hU n l) (hM k) (hM l)
    simpa only [ContinuousLinearMap.comp_apply, sub_add_cancel, zero_add] using (he.add (hPair k l b hb hb0))
  have ht := projectionFullSchwartz_defectPairing_tendsto μ x ξ N hx hξ hN a χ ha ha0
    hχReal hχm hχ hχc g hg gLp χ₀ hgCut (‖symbolCLM ρ‖ * B) hG hWeakG hPairG i j
  let UProj (n : ℕ) (k : OrderedPair) :=
    (projectionFullSchwartz (fun p q => w n (p,q)) k.1 k.2).toLp 2 volume
  have hCom (k : OrderedPair) : Tendsto (fun n => UProj n k - V n k) atTop (𝓝 0) := by
    have h := projectionFullSchwartz_halfDensity_sub_tendsto_zero ρ d hρ
      (fun n p q => f n (p,q)) (fun n p q => hf n (p,q)) (fun n p q => fLp n (p,q))
      χ₀ (fun n p q => hCut n (p,q)) B (fun n p q => hB n (p,q)) (fun p q => hWeak (p,q))
    exact (tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 h) k.1)) k.2
  have hVP (n : ℕ) (k : OrderedPair) : ‖V n k‖ ≤
      ‖symbolCLM ρ‖ * (‖projectionFullL2‖ * B) := by
    apply ((symbolCLM ρ).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply norm_projEntry_toLp_le
    intro p q
    exact (norm_realSchwartz_toLp (f n (p,q)) (hf n (p,q)) χ₀
      (hCut n (p,q)) (fLp n (p,q))).trans_le (hB n (p,q))
  have hUP (n : ℕ) (k : OrderedPair) : ‖UProj n k‖ ≤ ‖projectionFullL2‖ * (‖symbolCLM ρ‖ * B) :=
    norm_projEntry_toLp_le (fun p q => w n (p,q)) _ (fun p q => hU n (p,q)) k.1 k.2
  have hShift := defectPairing_sub_tendsto_zero_of_strong_errors
    ((symbolCLM χ).comp (fourierMultiplier a))
    (fun n => V n i) (fun n => V n j) (fun n => UProj n i) (fun n => UProj n j)
    _ _ (fun n => hVP n i) (fun n => hUP n j) (hCom i) (hCom j)
  change Tendsto (fun n => inner ℂ (UProj n i) (symbolCLM χ (fourierMultiplier a (UProj n j)))) atTop _ at ht
  simpa only [ContinuousLinearMap.comp_apply, sub_sub_cancel, sub_zero] using ht.sub hShift

end Burnett.P01
