import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualCyclicFourier
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFixedTestWindow

set_option autoImplicit false
set_option maxRecDepth 6700
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum)
open scoped ComplexConjugate ContDiff

/-- One actual fixed infrared window can be chosen before the chart
patches, and the same C02 test gives the homogeneous Ward Fourier form. -/
theorem wardActualThinGaugeFixedWindow_eq_fourier (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (D : ℝ) (hD : 0 ≤ D) (hJets : ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ Metric.sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n a ξ‖ ≤ D)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) :
    let b := fixedInfraredSymbol wardFixedTestCutoff 0 a
    let u := originalCubicThinScreen (inverseMatrix G) wi wo hm hη i o z hz
    let g := originalCubicGauge z hz
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    Integrable (wardCyclicCubicWeight G a H H H) ∧
      (wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q)).re =
        completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) b (u+g) :=
  wardActualThinGaugeCubicEnergy_eq_fourier G hG a ha hHom wardFixedTestCutoff 0
    wardFixedTestCutoff_real (by intro ξ; simp) wardFixedTestCutoff_profile_zero
    (by intro ξ _; simp [fixedRadianProfile]) (wardFixedTestCutoff_odd a hOdd)
    D hD (fun n hn => hJets n (hn.trans (by norm_num))) wi wo hm hη i o z hz

end Burnett.C02
