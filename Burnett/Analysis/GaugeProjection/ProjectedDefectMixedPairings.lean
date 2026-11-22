import Burnett.Analysis.GaugeProjection.ProjectedWeightedDefectPairings

set_option autoImplicit false
set_option maxHeartbeats 14000000

noncomputable section

namespace Burnett.P01

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.AngularCommutator (DegreeZero measurable_of_angular_smooth)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped ContDiff Topology Matrix ComplexOrder ENNReal NNReal ComplexConjugate

open private gaugePairTest gaugePairTest_smooth gaugePairTest_degreeZero
  projectionFullSchwartz_pair_eq_sum projectedCovariance_integrand
  from Burnett.Analysis.GaugeProjection.ProjectedDefectMatrixPairing
open private norm_realSchwartz_toLp norm_projEntry_toLp_le
  from Burnett.Analysis.GaugeProjection.ProjectedWeightedDefectPairings

private theorem projectionFullSchwartz_mixed_defectPairing_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (x : X → E) (ξ : X → E) (N : X → Matrix OrderedPair OrderedPair ℂ)
    (hx : Measurable x) (hξ : Measurable ξ)
    (hN : ∀ i j, Integrable (fun z => N z i j) μ)
    (a χ : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (ha0 : DegreeZero (a : E → ℂ))
    (hχReal : ∀ y, conj (χ y) = χ y)
    (hχm : Measurable (χ : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (f : Index → ℕ → OrderedPair → E → ℝ) (hf : ∀ s n k, ContDiff ℝ ∞ (f s n k))
    (fLp : ∀ s n k, MemLp (f s n k) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ s n k y, f s n k y ≠ 0 → (χ₀ : E → ℝ) y = 1)
    (B : ℝ) (hB : ∀ s n k, ‖(fLp s n k).toLp (f s n k)‖ ≤ B)
    (hWeak : ∀ s k (φ : D), Tendsto (fun n => ∫ y, f s n k y * (φ : E → ℝ) y) atTop (𝓝 0))
    (α β : Index)
    (hPair : let u := fun s n k => sourceSchwartz (hf s n k) χ₀ (hCut s n k)
      ∀ (k l : OrderedPair) (b : BoundedSymbol E), ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E) →
        DegreeZero (b : E → ℂ) →
        Tendsto (fun n => inner ℂ ((u α n k).toLp 2 volume)
          (symbolCLM χ (fourierMultiplier b ((u β n l).toLp 2 volume)))) atTop
          (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ)))
    (i j : OrderedPair) :
    let u := fun s n p q => sourceSchwartz (hf s n (p,q)) χ₀ (hCut s n (p,q))
    Tendsto (fun n =>
      inner ℂ ((projectionFullSchwartz (u α n) i.1 i.2).toLp 2 volume)
        (symbolCLM χ (fourierMultiplier a ((projectionFullSchwartz (u β n) j.1 j.2).toLp 2 volume)))) atTop
        (𝓝 (∫ z, χ (x z) * a (ξ z) *
          (principalGaugeProjectionMatrix (ξ z) * N z * (principalGaugeProjectionMatrix (ξ z))ᴴ) j i ∂μ)) := by
  intro u
  let b (k l : OrderedPair) := gaugePairTest a i j k l
  let U (n : ℕ) (k : OrderedPair) := gaugeProjectionSchwartzComponent i.1 i.2 k.1 k.2 (u α n k.1 k.2)
  let V (n : ℕ) (l : OrderedPair) := gaugeProjectionSchwartzComponent j.1 j.2 l.1 l.2 (u β n l.1 l.2)
  let F (k l : OrderedPair) (z : X) := χ (x z) * b k l (ξ z) * N z l k
  have ht (k l : OrderedPair) :
      Tendsto (fun n => inner ℂ ((U n k).toLp 2 volume)
        (symbolCLM χ (fourierMultiplier a ((V n l).toLp 2 volume)))) atTop (𝓝 (∫ z, F k l z ∂μ)) := by
    have hp := hPair k l (b k l) (gaugePairTest_smooth a ha i j k l) (gaugePairTest_degreeZero a ha0 i j k l)
    have hz := projectedDefectActualComponent_sub_tendsto_zero i.1 i.2 k.1 k.2 j.1 j.2 l.1 l.2 a χ
      hχReal hχ hχc (fun n => f α n k) (fun n => f β n l) (fun n => hf α n k) (fun n => hf β n l)
      (fun n => fLp α n k) (fun n => fLp β n l) χ₀ (fun n => hCut α n k) (fun n => hCut β n l)
      B B (fun n => hB α n k) (fun n => hB β n l) (hWeak α k) (hWeak β l)
    simpa only [U, V, F, b, gaugePairTest, sub_add_cancel, zero_add] using hz.add hp
  have hI (k l : OrderedPair) : Integrable (F k l) μ := by
    apply (hN l k).bdd_mul
    · have hm : Measurable (b k l : E → ℂ) :=
        measurable_of_angular_smooth _ (gaugePairTest_smooth a ha i j k l)
      exact ((hχm.comp hx).mul (hm.comp hξ)).aestronglyMeasurable
    · exact ⟨χ.bound * (b k l).bound, fun z => by
        rw [norm_mul]
        exact mul_le_mul (χ.norm_le _) ((b k l).norm_le _) (norm_nonneg _) χ.bound_nonneg⟩
  have hFin : Tendsto (fun n => ∑ k : OrderedPair, ∑ l : OrderedPair,
      inner ℂ ((U n k).toLp 2 volume) (symbolCLM χ (fourierMultiplier a ((V n l).toLp 2 volume))))
      atTop (𝓝 (∑ k : OrderedPair, ∑ l : OrderedPair, ∫ z, F k l z ∂μ)) :=
    tendsto_finset_sum _ (fun k _ => tendsto_finset_sum _ (fun l _ => ht k l))
  have hSum : (∑ k : OrderedPair, ∑ l : OrderedPair, ∫ z, F k l z ∂μ) =
      ∫ z, χ (x z) * a (ξ z) *
        (principalGaugeProjectionMatrix (ξ z) * N z * (principalGaugeProjectionMatrix (ξ z))ᴴ) j i ∂μ := by
    have hInner (k : OrderedPair) :
        (∑ l : OrderedPair, ∫ z, F k l z ∂μ) = ∫ z, ∑ l : OrderedPair, F k l z ∂μ :=
      (integral_finset_sum _ (fun l _ => hI k l)).symm
    simp only [hInner]
    rw [← integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hI k l))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => projectedCovariance_integrand a χ i j (x z) (ξ z) (N z))
  rw [hSum] at hFin
  simpa only [projectionFullSchwartz_pair_eq_sum, U, V] using hFin

/-- Transfer the angular pairing of two independently chosen weighted
input slots through the same actual cutoff projection. -/
theorem projectionFullSchwartz_weighted_mixed_defectPairing_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (x : X → E) (ξ : X → E) (N : X → Matrix OrderedPair OrderedPair ℂ)
    (hx : Measurable x) (hξ : Measurable ξ) (hN : ∀ i j, Integrable (fun z => N z i j) μ)
    (a χ : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (ha0 : DegreeZero (a : E → ℂ))
    (hχReal : ∀ y, conj (χ y) = χ y) (hχm : Measurable (χ : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (d : D) (ρ : BoundedSymbol E) (hρ : ∀ y, ρ y = ((d : E → ℝ) y : ℂ))
    (f : Index → ℕ → OrderedPair → E → ℝ) (hf : ∀ s n k, ContDiff ℝ ∞ (f s n k))
    (fLp : ∀ s n k, MemLp (f s n k) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ s n k y, f s n k y ≠ 0 → (χ₀ : E → ℝ) y = 1)
    (B : ℝ) (hB : ∀ s n k, ‖(fLp s n k).toLp (f s n k)‖ ≤ B)
    (hWeak : ∀ s k (φ : D), Tendsto (fun n => ∫ y, f s n k y * (φ : E → ℝ) y) atTop (𝓝 0))
    (W : Index → ℕ → OrderedPair → ComplexL2 E) (B₀ : ℝ) (hB₀ : ∀ s n k, ‖W s n k‖ ≤ B₀)
    (hErr : ∀ s k, Tendsto (fun n => symbolCLM ρ
      ((sourceSchwartz (hf s n k) χ₀ (hCut s n k)).toLp 2 volume) - W s n k) atTop (𝓝 0))
    (α β : Index)
    (hPair : ∀ (k l : OrderedPair) (b : BoundedSymbol E), ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E) →
      DegreeZero (b : E → ℂ) →
      Tendsto (fun n => inner ℂ (W α n k) (symbolCLM χ (fourierMultiplier b (W β n l)))) atTop
        (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ))) (i j : OrderedPair) :
    let u := fun s n p q => sourceSchwartz (hf s n (p,q)) χ₀ (hCut s n (p,q))
    let V := fun s n (k : OrderedPair) =>
      symbolCLM ρ ((projectionFullSchwartz (u s n) k.1 k.2).toLp 2 volume)
    Tendsto (fun n => inner ℂ (V α n i) (symbolCLM χ (fourierMultiplier a (V β n j)))) atTop
      (𝓝 (∫ z, χ (x z) * a (ξ z) *
        (principalGaugeProjectionMatrix (ξ z) * N z * (principalGaugeProjectionMatrix (ξ z))ᴴ) j i ∂μ)) := by
  intro u V
  let g (s : Index) (n : ℕ) (k : OrderedPair) (y : E) := (d : E → ℝ) y * f s n k y
  have hg (s : Index) (n : ℕ) (k : OrderedPair) : ContDiff ℝ ∞ (g s n k) := (test_smooth d).mul (hf s n k)
  have hgCut (s : Index) (n : ℕ) (k : OrderedPair) (y : E) (h : g s n k y ≠ 0) :
      (χ₀ : E → ℝ) y = 1 :=
    hCut s n k y (fun hh => h (mul_eq_zero.mpr (Or.inr hh)))
  have gLp (s : Index) (n : ℕ) (k : OrderedPair) : MemLp (g s n k) 2 volume := by
    apply (fLp s n k).of_le_mul (c := ρ.bound) (hg s n k).continuous.aestronglyMeasurable
    filter_upwards with y
    change ‖(d : E → ℝ) y * f s n k y‖ ≤ _
    rw [norm_mul]
    have hd : ‖(d : E → ℝ) y‖ ≤ ρ.bound := by
      simpa only [hρ, Complex.norm_real] using ρ.norm_le y
    exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  let w (s : Index) (n : ℕ) (k : OrderedPair) := sourceSchwartz (hg s n k) χ₀ (hgCut s n k)
  let U (s : Index) (n : ℕ) (k : OrderedPair) := (w s n k).toLp 2 volume
  have hEq (s : Index) (n : ℕ) (k : OrderedPair) :
      U s n k = symbolCLM ρ ((sourceSchwartz (hf s n k) χ₀ (hCut s n k)).toLp 2 volume) := by
    let F := sourceSchwartz (hf s n k) χ₀ (hCut s n k)
    apply Lp.ext
    filter_upwards [(w s n k).coeFn_toLp 2 volume, F.coeFn_toLp 2 volume,
      symbolL2_ae ρ (F.toLp 2 volume)] with y h₁ h₂ h₃
    change _ = symbolL2 ρ (F.toLp 2 volume) y
    rw [h₁, h₃, h₂, hρ]
    exact Complex.ofReal_mul _ _
  have hU (s : Index) (n : ℕ) (k : OrderedPair) : ‖U s n k‖ ≤ ‖symbolCLM ρ‖ * B := by
    rw [hEq]
    apply ((symbolCLM ρ).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_realSchwartz_toLp (f s n k) (hf s n k) χ₀ (hCut s n k) (fLp s n k)).trans_le (hB s n k)
  have hG (s : Index) (n : ℕ) (k : OrderedPair) :
      ‖(gLp s n k).toLp (g s n k)‖ ≤ ‖symbolCLM ρ‖ * B := by
    rw [← norm_realSchwartz_toLp (g s n k) (hg s n k) χ₀ (hgCut s n k) (gLp s n k)]
    exact hU s n k
  have hWeakG (s : Index) (k : OrderedPair) :
      ∀ (φ : D), Tendsto (fun n => ∫ y, g s n k y * (φ : E → ℝ) y) atTop (𝓝 0) := by
    intro φ
    let ψ : D := ⟨fun y => d.val y * φ.val y, (test_smooth d).mul (test_smooth φ),
      (test_compactSupport d).mul_right⟩
    convert hWeak s k ψ using 1
    funext n
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      change d.val y * f s n k y * φ.val y = f s n k y * (d.val y * φ.val y)
      ring)
  have hM (s : Index) (k : OrderedPair) : Tendsto (fun n => U s n k - W s n k) atTop (𝓝 0) := by
    simp only [hEq]
    exact hErr s k
  have hPairG (k l : OrderedPair) (b : BoundedSymbol E)
      (hb : ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E)) (hb0 : DegreeZero (b : E → ℂ)) :
      Tendsto (fun n => inner ℂ (U α n k) (symbolCLM χ (fourierMultiplier b (U β n l)))) atTop
        (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ)) := by
    have he := defectPairing_sub_tendsto_zero_of_strong_errors
      ((symbolCLM χ).comp (fourierMultiplier b))
      (fun n => W α n k) (fun n => W β n l) (fun n => U α n k) (fun n => U β n l)
      B₀ (‖symbolCLM ρ‖ * B) (fun n => hB₀ α n k) (fun n => hU β n l) (hM α k) (hM β l)
    simpa only [ContinuousLinearMap.comp_apply, sub_add_cancel, zero_add] using he.add (hPair k l b hb hb0)
  have ht := projectionFullSchwartz_mixed_defectPairing_tendsto μ x ξ N hx hξ hN a χ ha ha0
    hχReal hχm hχ hχc g hg gLp χ₀ hgCut (‖symbolCLM ρ‖ * B) hG hWeakG α β hPairG i j
  let UProj (s : Index) (n : ℕ) (k : OrderedPair) :=
    (projectionFullSchwartz (fun p q => w s n (p,q)) k.1 k.2).toLp 2 volume
  have hCom (s : Index) (k : OrderedPair) : Tendsto (fun n => UProj s n k - V s n k) atTop (𝓝 0) := by
    have h := projectionFullSchwartz_halfDensity_sub_tendsto_zero ρ d hρ
      (fun n p q => f s n (p,q)) (fun n p q => hf s n (p,q)) (fun n p q => fLp s n (p,q))
      χ₀ (fun n p q => hCut s n (p,q)) B (fun n p q => hB s n (p,q)) (fun p q => hWeak s (p,q))
    exact (tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 h) k.1)) k.2
  have hVP (s : Index) (n : ℕ) (k : OrderedPair) : ‖V s n k‖ ≤
      ‖symbolCLM ρ‖ * (‖projectionFullL2‖ * B) := by
    apply ((symbolCLM ρ).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply norm_projEntry_toLp_le
    intro p q
    exact (norm_realSchwartz_toLp (f s n (p,q)) (hf s n (p,q)) χ₀
      (hCut s n (p,q)) (fLp s n (p,q))).trans_le (hB s n (p,q))
  have hUP (s : Index) (n : ℕ) (k : OrderedPair) : ‖UProj s n k‖ ≤ ‖projectionFullL2‖ * (‖symbolCLM ρ‖ * B) :=
    norm_projEntry_toLp_le (fun p q => w s n (p,q)) _ (fun p q => hU s n (p,q)) k.1 k.2
  have hShift := defectPairing_sub_tendsto_zero_of_strong_errors
    ((symbolCLM χ).comp (fourierMultiplier a))
    (fun n => V α n i) (fun n => V β n j) (fun n => UProj α n i) (fun n => UProj β n j)
    _ _ (fun n => hVP α n i) (fun n => hUP β n j) (hCom α i) (hCom β j)
  change Tendsto (fun n => inner ℂ (UProj α n i) (symbolCLM χ (fourierMultiplier a (UProj β n j)))) atTop _ at ht
  simpa only [ContinuousLinearMap.comp_apply, sub_sub_cancel, sub_zero] using ht.sub hShift

end Burnett.P01
