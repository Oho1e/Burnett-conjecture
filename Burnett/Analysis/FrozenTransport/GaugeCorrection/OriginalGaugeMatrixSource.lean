import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeActualOperators
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalProjectedSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxRecDepth 4800

noncomputable section
namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A07 Burnett.A08 Burnett.C02
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.V06 (ScreenMatrix)
open scoped ContDiff Matrix ENNReal ComplexConjugate

/-- One family of original matrix operators handles every high input and test.
At fixed real low field the operator in the transposed entry is the true tested
adjoint, including in the exact two-source identity for the transport numerator. -/
theorem exists_originalScreenGauge_matrix_mixedSource (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (boundθ : ∀ t, |θ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16) (g : ScreenMatrix) (hg : gᵀ = g)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (innerRadius outerRadius : ℝ) :
    let m := inverseMatrix g
    let C := gaugeFrozenContraction m
    let screen := (thinScreenAngular m i o hm hη innerRadius outerRadius).matrix
    let cut := gaugeCorrectionInfrared
    ∃ K : TensorSlot → TensorSlot → ℝ, (∀ I J, 0 ≤ K I J) ∧
    ∀ (z : ProjectionSchwartzMatrix), (∀ k l x, conj (z k l x) = z k l x) →
    ∃ T : TensorSlot → TensorSlot → SchwartzMap E ℂ → FirstOrderLp 2,
      (∀ I J, (∀ u v : SchwartzMap E ℂ,
        inner ℂ (v.toLp 2 volume) (T I J u) = originalGaugeRadianPair θ cut cut κ m (metricDensity g) a C screen z I J u v ∧
        inner ℂ (v.toLp 2 volume) (T I J u) = inner ℂ (T J I v) (u.toLp 2 volume)) ∧
        ∀ u, ‖T I J u‖ ≤ K I J * (∑ k : TensorSlot, ‖(Burnett.C03.projectedGaugeComplement z k.1 k.2).toLp 4 volume‖) *
          highDerivativeLp4Sum u) ∧
      ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients),
      (∀ r s x, A.entry r s x = ((m r s + d r s x : ℝ) : ℂ)) →
      ∀ (I J : TensorSlot) (U V : ProjectionSchwartzMatrix),
      let u := projectionFullSchwartz U J.1 J.2
      let v := projectionFullSchwartz V I.1 I.2
      let N (x : Joint) := (gaugeTriadCutoff θ cut cut κ x.1 x.2 : ℂ) *
        lowGaugeTransportCoefficient m (metricDensity g) a (originalLowGaugePotential z) C screen x.1 x.2 I J *
        radianFourier u x.2 * conj (radianFourier v (x.2+x.1))
      Integrable N ∧ (tau^8)⁻¹ • ∫ x, N x = Complex.I *
        (inner ℂ (projectedSourceDivergenceL2 A (projectionFullSchwartz V) I.1 I.2) (T I J u) -
        inner ℂ (T J I v) (projectedSourceDivergenceL2 A (projectionFullSchwartz U) J.1 J.2) -
        weakDivergenceCommutatorPair d (T I J) u v) := by
  classical
  intro m C screen cut
  let scr := thinScreenAngular m i o hm hη innerRadius outerRadius
  choose K hK op using fun I J : TensorSlot => exists_originalGaugeRawEntry_operator θ hθ κ hκ hSmall hcut m
    (metricDensity g) a ha hOdd hHom C screen scr.smooth scr.degree I J
  refine ⟨K,hK,?_⟩
  intro z hReal
  choose T rep bound using fun I J : TensorSlot => op I J z
  have hmSym : (m : ScreenMatrix)ᵀ = m := by
    change g⁻¹ᵀ = g⁻¹
    rw [Matrix.transpose_nonsing_inv, hg]
  have hC : (C : Matrix TensorSlot TensorSlot ℝ)ᵀ = C := gaugeFrozenContraction_symmetric m hmSym
  refine ⟨T, fun I J => ⟨fun u v => ⟨rep I J u v, originalGaugeRepresentatives_dual θ cut cut κ m
    (metricDensity g) a hOdd C hC screen z hReal I J (T I J) (T J I) (rep I J) (rep J I) u v⟩,bound I J⟩, ?_⟩
  intro d A hA I J U V
  have split := originalScreenGauge_transport_eq_mixedSource θ hθ.continuous.measurable hcut boundθ κ hκ hSmall
    g hg a ha hOdd hHom i o hm hη innerRadius outerRadius z hReal I J (T I J) (T J I) d (rep I J) (rep J I) U V
  rw [projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A m d hA V I.1 I.2,
    projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A m d hA U J.1 J.2]
  exact split

end Burnett.V08
