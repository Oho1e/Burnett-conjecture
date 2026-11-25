import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeMatrixSource

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4500

noncomputable section
namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01 Burnett.A07 Burnett.A08 Burnett.C02
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.V06 (ScreenMatrix)
open scoped ContDiff Matrix BigOperators ENNReal ComplexConjugate
open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

private def rawHighLinearMap (T S : SchwartzMap E ℂ → FirstOrderLp 2)
    (dual : ∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u) = inner ℂ (S v) (u.toLp 2 volume)) :
    SchwartzMap E ℂ →ₗ[ℂ] FirstOrderLp 2 where
  toFun := T
  map_add' u v := by
    apply inner_eq_of_schwartz
    intro w
    have split : (u+v).toLp 2 volume = u.toLp 2 volume + v.toLp 2 volume :=
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_add _ _
    simp only [inner_add_right, dual, split]
  map_smul' t u := by
    apply inner_eq_of_schwartz
    intro w
    have split : (t • u).toLp 2 volume = t • u.toLp 2 volume :=
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul _ _
    change inner ℂ (w.toLp 2 volume) (T (t • u)) = inner ℂ (w.toLp 2 volume) (t • T u)
    simp only [inner_smul_right, dual, split]

private theorem integral_matrix_sum {f : TensorSlot → TensorSlot → Joint → ℂ} {r : TensorSlot → TensorSlot → ℂ}
    (h : ∀ i j, Integrable (f i j) ∧ (tau^8)⁻¹ • ∫ x, f i j x = Complex.I * r i j) :
    Integrable (fun x => ∑ i, ∑ j, f i j x) ∧
      (tau^8)⁻¹ • ∫ x, ∑ i, ∑ j, f i j x = Complex.I * (∑ i, ∑ j, r i j) := by
  have row (i : TensorSlot) : Integrable (fun x => ∑ j, f i j x) := integrable_finset_sum _ (fun j _ => (h i j).1)
  refine ⟨integrable_finset_sum _ (fun i _ => row i), ?_⟩
  rw [integral_finset_sum _ (fun i _ => row i), Finset.smul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => (h i j).1), Finset.smul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => (h i j).2)

/-- The full 16-by-16 gauge transport numerator is equal to the whole matrix
source pairing. Off-diagonal high entries occur with the transposed operator. -/
theorem exists_originalScreenGauge_fullSource (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (boundθ : ∀ t, |θ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16) (g : ScreenMatrix) (hg : gᵀ = g)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (innerRadius outerRadius : ℝ) (z : ProjectionSchwartzMatrix) (hReal : ∀ k l x, conj (z k l x) = z k l x) :
    let m := inverseMatrix g
    let C := gaugeFrozenContraction m
    let S := (thinScreenAngular m i o hm hη innerRadius outerRadius).matrix
    let cut := gaugeCorrectionInfrared
    ∃ T : TensorSlot → TensorSlot → (SchwartzMap E ℂ →ₗ[ℂ] FirstOrderLp 2),
      (∀ I J (u v : SchwartzMap E ℂ),
        inner ℂ (v.toLp 2 volume) (T I J u) = originalGaugeRadianPair θ cut cut κ m (metricDensity g) a C S z I J u v ∧
        inner ℂ (v.toLp 2 volume) (T I J u) = inner ℂ (T J I v) (u.toLp 2 volume)) ∧
      ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients),
      (∀ r s x, A.entry r s x = ((m r s + d r s x : ℝ) : ℂ)) →
      ∀ U V : ProjectionSchwartzMatrix,
      let u := projectionFullSchwartz U
      let v := projectionFullSchwartz V
      let N (x : Joint) := ∑ I : TensorSlot, ∑ J : TensorSlot,
        (gaugeTriadCutoff θ cut cut κ x.1 x.2 : ℂ) *
        lowGaugeTransportCoefficient m (metricDensity g) a (originalLowGaugePotential z) C S x.1 x.2 I J *
        radianFourier (u J.1 J.2) x.2 * conj (radianFourier (v I.1 I.2) (x.2+x.1))
      Integrable N ∧ (tau^8)⁻¹ • ∫ x, N x = Complex.I * (∑ I : TensorSlot, ∑ J : TensorSlot,
        (inner ℂ (projectedSourceDivergenceL2 A v I.1 I.2) (T I J (u J.1 J.2)) -
        inner ℂ (T J I (v I.1 I.2)) (projectedSourceDivergenceL2 A u J.1 J.2) -
        weakDivergenceCommutatorPair d (T I J) (u J.1 J.2) (v I.1 I.2))) := by
  intro m C S cut
  obtain ⟨_,_,ops⟩ := exists_originalScreenGauge_matrix_mixedSource θ hθ hcut boundθ κ hκ hSmall g hg a ha
    hOdd hHom i o hm hη innerRadius outerRadius
  obtain ⟨T,rep,rows⟩ := ops z hReal
  let L (I J : TensorSlot) := rawHighLinearMap (T I J) (T J I) (fun u v => ((rep I J).1 u v).2)
  refine ⟨L, fun I J u v => (rep I J).1 u v, ?_⟩
  intro d A hA U V
  exact integral_matrix_sum (fun I J => rows d A hA I J U V)

end Burnett.V08
