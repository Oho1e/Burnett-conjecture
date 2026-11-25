import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeTransportIntegral
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalChartGaugeAdjoint

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4500

noncomputable section
namespace Burnett.V08

open MeasureTheory Matrix Burnett.P01 Burnett.A06 Burnett.A07 Burnett.A08 Burnett.C02
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.V06 (ScreenMatrix)
open scoped ContDiff Matrix ComplexConjugate ENNReal

/-- A forward representative of the transposed entry with exchanged masks is the
tested adjoint of the original entry. The two high fields are independent. -/
theorem originalGaugeRepresentatives_dual (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (hC : Cᵀ = C) (S : GaugeScreen)
    (z : ProjectionSchwartzMatrix) (hReal : ∀ k l x, conj (z k l x) = z k l x)
    (i j : TensorSlot) (T Tstar : SchwartzMap E ℂ → FirstOrderLp 2)
    (hT : ∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u) =
      originalGaugeRadianPair θ hi ho κ m w a C S z i j u v)
    (hTstar : ∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (Tstar u) =
      originalGaugeRadianPair θ ho hi κ m w a C S z j i u v) (u v : SchwartzMap E ℂ) :
    inner ℂ (v.toLp 2 volume) (T u) = inner ℂ (Tstar v) (u.toLp 2 volume) := by
  have eq := originalGaugeRadianPair_adjoint θ hi ho κ m w a hOdd C hC S z hReal i j u v
  rw [← hT u v, ← hTstar v u] at eq
  simpa only [inner_conj_symm, starRingEnd_self_apply] using (congrArg (fun t : ℂ => conj t) eq).symm

/-- On the original two projected high fields, an off-diagonal component of the
transport integral equals the tested source expression with the actual adjoint
entry. The representation hypotheses name precisely the two Fourier forms. -/
theorem originalScreenGauge_transport_eq_mixedSource (θ : ℝ → ℝ) (hθ : Measurable θ)
    (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (boundθ : ∀ t, |θ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16) (g : ScreenMatrix) (hg : gᵀ = g)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η)
    (innerRadius outerRadius : ℝ) (z : ProjectionSchwartzMatrix)
    (hReal : ∀ k l x, conj (z k l x) = z k l x) (I J : TensorSlot)
    (T Tstar : SchwartzMap E ℂ → FirstOrderLp 2) (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) :
    let m := inverseMatrix g
    let C := gaugeFrozenContraction m
    let S := (thinScreenAngular m i o hm hη innerRadius outerRadius).matrix
    let form := originalGaugeRadianPair θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m (metricDensity g) a C S z
    (∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u) = form I J u v) →
    (∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (Tstar u) = form J I u v) →
    ∀ U V : ProjectionSchwartzMatrix,
    let u := projectionFullSchwartz U J.1 J.2
    let v := projectionFullSchwartz V I.1 I.2
    let N (x : Joint) := (gaugeTriadCutoff θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ x.1 x.2 : ℂ) *
      lowGaugeTransportCoefficient m (metricDensity g) a (originalLowGaugePotential z) C S x.1 x.2 I J *
      radianFourier u x.2 * conj (radianFourier v (x.2+x.1))
    let source (f : SchwartzMap E ℂ) := (constantWave m f + schwartzDivergence d f).toLp 2 volume
    Integrable N ∧ (tau^8)⁻¹ • ∫ x, N x = Complex.I *
      (inner ℂ (source v) (T u) - inner ℂ (Tstar v) (source u) - weakDivergenceCommutatorPair d T u v) := by
  intro m C S form hT hTstar U V u v N source
  have hmSym : (m : ScreenMatrix)ᵀ = m := by
    change g⁻¹ᵀ = g⁻¹
    rw [Matrix.transpose_nonsing_inv, hg]
  have dual := originalGaugeRepresentatives_dual θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ
    m (metricDensity g) a hOdd C (gaugeFrozenContraction_symmetric m hmSym) S z hReal I J T Tstar hT hTstar
  obtain ⟨meas, B, hB, order⟩ := originalScreenGauge_entry_control θ hθ hcut boundθ κ hκ hSmall g a
    ha hOdd hHom i o hm hη innerRadius outerRadius I J
  have raw := weakConstantWaveCommutatorPair_eq_originalGauge_transport θ gaugeCorrectionInfrared
    gaugeCorrectionInfrared κ m (metricDensity g) a C S z I J B hB meas order T hT u v
  have split := weakConstantWaveCommutatorPair_eq_mixedSource m d T Tstar dual u v
  exact ⟨raw.1, raw.2.symm.trans (congrArg (Complex.I*·) split)⟩

end Burnett.V08
