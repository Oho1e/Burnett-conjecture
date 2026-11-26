import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeScreenContraction
import Burnett.Analysis.CubicEnergy.AngularCorrection.FixedInfraredSchwartzPairing
import Burnett.Analysis.GaugeProjection.MatrixProjectionSlots

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Burnett.V08

open MeasureTheory Burnett.A06 Burnett.A07 Burnett.P01 Burnett.Fourier
open Burnett.A02.FrequencySplit (E Joint radianFourier radianFourier_scaled tau)
open scoped ContDiff FourierTransform

theorem gaugeCorrectionInfrared_smooth : ContDiff ℝ ∞ gaugeCorrectionInfrared :=
  gaugeProjectionInfrared_contDiff.comp (contDiff_const.mul contDiff_id)

theorem gaugeCorrectionInfrared_zero (s : ℝ) (hs : s ≤ 1/2) : gaugeCorrectionInfrared s = 0 :=
  gaugeProjectionInfrared_zero (by linarith)

theorem gaugeCorrectionInfrared_one (s : ℝ) (hs : 1 ≤ s) : gaugeCorrectionInfrared s = 1 :=
  gaugeProjectionInfrared_one (by linarith)

def gaugeCorrectionInfraredSchwartz (w : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  fixedInfraredSchwartz gaugeCorrectionInfrared gaugeCorrectionInfrared_smooth (1/2) 1
    (by norm_num) gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one w

theorem gaugeCorrectionInfraredSchwartz_fourier (w : SchwartzMap E ℂ) (p : E) :
    radianFourier (gaugeCorrectionInfraredSchwartz w) p = (gaugeCorrectionInfrared ‖p‖ : ℂ) * radianFourier w p :=
  fixedInfraredSchwartz_radianFourier _ _ _ _ _ _ _ _ _

private def gaugeCorrectionBoundedSymbol : BoundedSymbol E :=
  { toFun := fun ν => (gaugeCorrectionInfrared ‖tau • ν‖ : ℂ)
    measurable := (Complex.continuous_ofReal.comp (gaugeCorrectionInfrared_smooth.continuous.comp
      (continuous_const.smul continuous_id).norm)).aestronglyMeasurable
    bound := 1
    bound_nonneg := zero_le_one
    norm_le := fun ν => by
      rw [Complex.norm_real, gaugeCorrectionInfrared, gaugeProjectionInfrared,
        Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _ }

def gaugeCorrectionOutputL2 : ComplexL2 E →L[ℂ] ComplexL2 E := fourierMultiplier gaugeCorrectionBoundedSymbol

theorem gaugeCorrectionOutputL2_schwartz (w : SchwartzMap E ℂ) :
    gaugeCorrectionOutputL2 (w.toLp 2 volume) = (gaugeCorrectionInfraredSchwartz w).toLp 2 volume := by
  apply fourierL2Equiv.injective
  unfold gaugeCorrectionOutputL2
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [symbolL2_ae gaugeCorrectionBoundedSymbol (fourierL2Equiv (w.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae w, fourierL2Equiv_schwartz_ae (gaugeCorrectionInfraredSchwartz w)] with ν ha hf hg
  rw [ha,hf,hg, ← radianFourier_scaled, ← radianFourier_scaled, gaugeCorrectionInfraredSchwartz_fourier]
  rfl

theorem gaugeCorrectionOutput_move (b : Joint → ℂ) (f u v : SchwartzMap E ℂ) :
    radianHighPair (fun x => (gaugeCorrectionInfrared ‖x.2+x.1‖ : ℂ) * b x) f u v =
      radianHighPair b f u (gaugeCorrectionInfraredSchwartz v) := by
  simpa only [Complex.real_smul, gaugeCorrectionInfraredSchwartz] using
    radianHighPair_fixedInfrared_on_output gaugeCorrectionInfrared gaugeCorrectionInfrared_smooth (1/2) 1
      (by norm_num) gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one b f u v

end Burnett.V08
