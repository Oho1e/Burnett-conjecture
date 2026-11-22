import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents
import Burnett.Analysis.GaugeProjection.ProjectedPhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 8500000

noncomputable section

namespace Burnett.P01

open Matrix MeasureTheory Filter Set Burnett.Fourier
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (D)
open Burnett.Microlocal.AngularCommutator (DegreeZero measurable_of_angular_smooth)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff ComplexConjugate Matrix Topology

private def gaugePairTest (a : BoundedSymbol E) (i j k l : OrderedPair) : BoundedSymbol E :=
  projectedPairingSymbol (principalProjectionComponentSymbol i.1 i.2 k.1 k.2) a
    (principalProjectionComponentSymbol j.1 j.2 l.1 l.2)

private theorem gaugePairTest_apply (a : BoundedSymbol E) (i j k l : OrderedPair) (ξ : E) :
    gaugePairTest a i j k l ξ =
      principalGaugeProjectionMatrix ξ i k * (a ξ * principalGaugeProjectionMatrix ξ j l) := by
  simp only [gaugePairTest, projectedPairingSymbol, principalGaugeProjectionMatrix,
    principalProjectionComponentSymbol_apply]

private theorem gaugePairTest_smooth (a : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (i j k l : OrderedPair) :
    ContDiffOn ℝ ∞ (gaugePairTest a i j k l : E → ℂ) ({0}ᶜ : Set E) := by
  rw [show (gaugePairTest a i j k l : E → ℂ) = (fun ξ =>
      (gaugeProjectionSymbol i.1 i.2 k.1 k.2 ξ : ℂ) *
        (a ξ * (gaugeProjectionSymbol j.1 j.2 l.1 l.2 ξ : ℂ))) from
      funext (gaugePairTest_apply a i j k l)]
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (gaugeProjectionSymbol_contDiffOn i.1 i.2 k.1 k.2)).mul
    (ha.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (gaugeProjectionSymbol_contDiffOn j.1 j.2 l.1 l.2)))

private theorem gaugePairTest_degreeZero (a : BoundedSymbol E)
    (ha : DegreeZero (a : E → ℂ)) (i j k l : OrderedPair) :
    DegreeZero (gaugePairTest a i j k l : E → ℂ) := by
  intro r hr ξ
  simp only [gaugePairTest_apply, principalGaugeProjectionMatrix, gaugeProjectionSymbol_scale _ _ _ _ r hr,
    ha r hr ξ]

private theorem projectionFullSchwartz_pair_eq_sum
    (a χ : BoundedSymbol E) (u v : ProjectionSchwartzMatrix) (i j : OrderedPair) :
    inner ℂ ((projectionFullSchwartz u i.1 i.2).toLp 2 volume)
      (symbolCLM χ (fourierMultiplier a ((projectionFullSchwartz v j.1 j.2).toLp 2 volume))) =
      ∑ k : OrderedPair, ∑ l : OrderedPair,
        inner ℂ ((gaugeProjectionSchwartzComponent i.1 i.2 k.1 k.2 (u k.1 k.2)).toLp 2 volume)
          (symbolCLM χ (fourierMultiplier a
            ((gaugeProjectionSchwartzComponent j.1 j.2 l.1 l.2 (v l.1 l.2)).toLp 2 volume))) := by
  let U (k : OrderedPair) := gaugeProjectionSchwartzComponent i.1 i.2 k.1 k.2 (u k.1 k.2)
  let V (l : OrderedPair) := gaugeProjectionSchwartzComponent j.1 j.2 l.1 l.2 (v l.1 l.2)
  have hU : projectionFullSchwartz u i.1 i.2 = ∑ k : OrderedPair, U k := by
    rw [Fintype.sum_prod_type]
    rfl
  have hV : projectionFullSchwartz v j.1 j.2 = ∑ k : OrderedPair, V k := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hU, hV]
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)
  change inner ℂ (L (∑ k, U k)) (symbolCLM χ (fourierMultiplier a (L (∑ l, V l)))) = _
  simp only [map_sum, sum_inner, inner_sum]
  exact Finset.sum_comm

private theorem projectedCovariance_integrand (a χ : BoundedSymbol E) (i j : OrderedPair)
    (x ξ : E) (N : Matrix OrderedPair OrderedPair ℂ) :
    (∑ k : OrderedPair, ∑ l : OrderedPair, χ x * gaugePairTest a i j k l ξ * N l k) =
      χ x * a ξ *
        (principalGaugeProjectionMatrix ξ * N * (principalGaugeProjectionMatrix ξ)ᴴ) j i := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, principalGaugeProjectionMatrix,
    gaugePairTest_apply, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- On the same subsequence and the same angular trace, the actual projected
ordered pairings have the covariance obtained by applying the principal
projection to both original matrix slots. The original tested pairing uses
the entry N j i for the first slot i and second slot j. -/
theorem projectionFullSchwartz_defectPairing_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (x : X → E) (ξ : X → E) (N : X → Matrix OrderedPair OrderedPair ℂ)
    (hx : Measurable x) (hξ : Measurable ξ)
    (hN : ∀ i j, Integrable (fun z => N z i j) μ)
    (a χ : BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (a : E → ℂ) ({0}ᶜ : Set E)) (ha0 : DegreeZero (a : E → ℂ))
    (hχReal : ∀ y, conj (χ y) = χ y)
    (hχm : Measurable (χ : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (f : ℕ → OrderedPair → E → ℝ) (hf : ∀ n k, ContDiff ℝ ∞ (f n k))
    (fLp : ∀ n k, MemLp (f n k) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ n k y, f n k y ≠ 0 → (χ₀ : E → ℝ) y = 1)
    (B : ℝ) (hB : ∀ n k, ‖(fLp n k).toLp (f n k)‖ ≤ B)
    (hWeak : ∀ k (φ : D), Tendsto (fun n => ∫ y, f n k y * (φ : E → ℝ) y) atTop (𝓝 0))
    (hPair : let u := fun n k => sourceSchwartz (hf n k) χ₀ (hCut n k)
      ∀ (k l : OrderedPair) (b : BoundedSymbol E), ContDiffOn ℝ ∞ (b : E → ℂ) ({0}ᶜ : Set E) →
        DegreeZero (b : E → ℂ) →
        Tendsto (fun n => inner ℂ ((u n k).toLp 2 volume)
          (symbolCLM χ (fourierMultiplier b ((u n l).toLp 2 volume)))) atTop
          (𝓝 (∫ z, χ (x z) * b (ξ z) * N z l k ∂μ)))
    (i j : OrderedPair) :
    let u := fun n a b => sourceSchwartz (hf n (a,b)) χ₀ (hCut n (a,b))
    Tendsto (fun n =>
      inner ℂ ((projectionFullSchwartz (u n) i.1 i.2).toLp 2 volume)
        (symbolCLM χ (fourierMultiplier a ((projectionFullSchwartz (u n) j.1 j.2).toLp 2 volume)))) atTop
        (𝓝 (∫ z, χ (x z) * a (ξ z) *
          (principalGaugeProjectionMatrix (ξ z) * N z * (principalGaugeProjectionMatrix (ξ z))ᴴ) j i ∂μ)) := by
  intro u
  let b (k l : OrderedPair) := gaugePairTest a i j k l
  let U (n : ℕ) (k : OrderedPair) := gaugeProjectionSchwartzComponent i.1 i.2 k.1 k.2 (u n k.1 k.2)
  let V (n : ℕ) (l : OrderedPair) := gaugeProjectionSchwartzComponent j.1 j.2 l.1 l.2 (u n l.1 l.2)
  let F (k l : OrderedPair) (z : X) := χ (x z) * b k l (ξ z) * N z l k
  have ht (k l : OrderedPair) :
      Tendsto (fun n => inner ℂ ((U n k).toLp 2 volume)
        (symbolCLM χ (fourierMultiplier a ((V n l).toLp 2 volume)))) atTop (𝓝 (∫ z, F k l z ∂μ)) := by
    have hp := hPair k l (b k l) (gaugePairTest_smooth a ha i j k l) (gaugePairTest_degreeZero a ha0 i j k l)
    have hz := projectedDefectActualComponent_sub_tendsto_zero i.1 i.2 k.1 k.2 j.1 j.2 l.1 l.2 a χ
      hχReal hχ hχc (fun n => f n k) (fun n => f n l) (fun n => hf n k) (fun n => hf n l)
      (fun n => fLp n k) (fun n => fLp n l) χ₀ (fun n => hCut n k) (fun n => hCut n l)
      B B (fun n => hB n k) (fun n => hB n l) (hWeak k) (hWeak l)
    have h := hz.add hp
    simpa only [U, V, F, b, gaugePairTest, sub_add_cancel, zero_add] using h
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
      atTop (𝓝 (∑ k : OrderedPair, ∑ l : OrderedPair, ∫ z, F k l z ∂μ)) := by
    exact tendsto_finset_sum _ (fun k _ => tendsto_finset_sum _ (fun l _ => ht k l))
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

end Burnett.P01
