import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeScreenContraction
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeRawOrder
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V08

open MeasureTheory Matrix Burnett.P01 Burnett.C02 Burnett.Geometry
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.MaximalChart
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.V06 (ScreenMatrix)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix ComplexConjugate

/-- With both actual radian regularizers and the paper's screen, the scalar raw
symbols are measurable and obey one common linear growth bound over the low index. -/
theorem originalScreenGauge_entry_control (θ : ℝ → ℝ) (hθ : Measurable θ)
    (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (boundθ : ∀ t, |θ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16)
    (g : ScreenMatrix) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0})
    (hOdd : ∀ x, a (-x) = -a x) (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) (I J : TensorSlot) :
    let m := inverseMatrix g
    let S := (thinScreenAngular m i o hm hη inner outer).matrix
    let b (k : TensorSlot) := gaugeRawEntry θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m
      (metricDensity g) a (gaugeFrozenContraction m) S k I J
    (∀ k, Measurable (b k)) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ k (x : Joint), ‖b k x‖ ≤ B*(1+‖x.1‖+‖x.2‖) := by
  intro m S b
  let scr := thinScreenAngular m i o hm hη inner outer
  have hReg : Measurable gaugeCorrectionInfrared :=
    gaugeProjectionInfrared_contDiff.continuous.measurable.comp (measurable_const.mul measurable_id)
  have hRegZero : gaugeCorrectionInfrared 0 = 0 := by
    apply gaugeProjectionInfrared_zero
    norm_num
  have hRegOne (s : ℝ) : |gaugeCorrectionInfrared s| ≤ 1 := by
    change |Real.smoothTransition (2*s-1)| ≤ 1
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  exact ⟨fun k => gaugeRawEntry_measurable θ _ _ κ m (metricDensity g) a _ S
    hθ hReg hReg ha scr.smooth k I J,
    exists_gaugeRawEntry_orderOne θ _ _ κ hκ hSmall hcut hRegZero boundθ hRegOne hRegOne
      m (metricDensity g) a _ S ha hOdd hHom scr.smooth scr.degree I J⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

theorem receivingCutoffFluctuation_gauge_real (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (n : ℕ) (k l : Fin 4) (x : E) :
    conj (receivingCutoffFluctuation B g hB hg c χ hχ n k l x) =
      receivingCutoffFluctuation B g hB hg c χ hχ n k l x := by
  exact Complex.conj_ofReal _

/-- The low tensor is the original real fluctuation on the stated subsequence.
The two high tensors remain independent and retain their original projectors. -/
theorem originalChartGaugeMatrixPair_adjoint (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (σ : ℕ → ℕ) (n : ℕ)
    (θ : ℝ → ℝ) (κ : ℝ) (frozen : ScreenMatrix) (hSym : frozenᵀ = frozen)
    (a : E → ℝ) (hOdd : ∀ x, a (-x) = -a x) (i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix frozen)) {η : ℝ} (hη : 0 < η)
    (inner outer : ℝ) (u v : ProjectionSchwartzMatrix) :
    let z := receivingCutoffFluctuation B g hB hg c χ hχ (σ n)
    originalScreenGaugeMatrixPair θ κ frozen a i o hm hη inner outer z v u =
      conj (originalScreenGaugeMatrixPair θ κ frozen a i o hm hη inner outer z u v) :=
  originalScreenGaugeMatrixPair_adjoint θ κ frozen hSym a hOdd i o hm hη inner outer _ u v
    (receivingCutoffFluctuation_gauge_real B g hB hg c χ hχ (σ n))

end Burnett.V08
