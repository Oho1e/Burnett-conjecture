import Burnett.Analysis.CubicEnergy.BilinearMultiplier.FourierConvention
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

abbrev tau : ℝ := 2 * Real.pi

/-- Fourier integral with the phase used in manuscript lines 539–560. -/
def radianFourier (f : E → ℂ) (ζ : E) : ℂ :=
  ∫ x, Complex.exp ((- (inner ℝ x ζ : ℝ) : ℂ) * Complex.I) * f x

theorem radianFourier_scaled (f : E → ℂ) (ν : E) :
    radianFourier f (tau • ν) = 𝓕 f ν := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [real_inner_smul_right, smul_eq_mul, neg_mul, tau,Complex.ofReal_neg]

def radianAction (b : E → ℝ) (v : SchwartzMap E ℂ) (x : E) : ℂ :=
  (tau^4)⁻¹ • ∫ ζ, Complex.exp ((inner ℝ ζ x : ℂ) * Complex.I) *
    ((b ζ : ℂ) * radianFourier v ζ)

theorem radianAction_eq_orderOne (b : E → ℝ) (v : SchwartzMap E ℂ) (x : E) :
    radianAction b v x = orderOneAction (fun ν => b (tau • ν)) v x := by
  let F := fun ζ : E => Complex.exp ((inner ℝ ζ x : ℂ)*Complex.I) * ((b ζ : ℂ)*radianFourier v ζ)
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure E) F tau
    (hR := (mul_pos (by norm_num) Real.pi_pos).le)
  unfold radianAction orderOneAction
  rw [dimE] at changeFreq
  rw [← changeFreq, Real.fourierIntegralInv_eq']
  apply integral_congr_ae
  filter_upwards with ν
  simp only [F,real_inner_smul_left,radianFourier_scaled,smul_eq_mul,tau]

def radianWeight (a : Joint → ℝ) (f v w : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  (a p : ℂ) * radianFourier f p.1 * radianFourier v p.2 * radianFourier w (-(p.1+p.2))

theorem jointVolume_haar : (volume : Measure Joint).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod E E]
  infer_instance

/-- The two four-dimensional frequency changes supply the paper's exact factor. -/
theorem radianWeight_integral (a : Joint → ℝ) (f v w : SchwartzMap E ℂ) :
    (tau^8)⁻¹ • (∫ p, radianWeight a f v w p) =
      ∫ p, bilinearFourierWeight (fun q => a (tau • q)) f v w p := by
  letI := jointVolume_haar
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod,dimE]
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint) (radianWeight a f v w) tau
    (hR := (mul_pos (by norm_num) Real.pi_pos).le)
  rw [dimJoint] at changeFreq
  rw [← changeFreq]
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianWeight,bilinearFourierWeight,Prod.smul_fst,Prod.smul_snd,← smul_add,← smul_neg,
    radianFourier_scaled]

end Burnett.A02.FrequencySplit
