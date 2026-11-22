import Burnett.Analysis.GaugeProjection.HodgeCommutator
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped BigOperators FourierTransform RealInnerProductSpace

/-- The actual vector Hodge projection, evaluated componentwise by the radian multiplier. -/
def hodgeTransverseAction (w : HodgeSchwartzField) (i : Fin 4) (x : E) : ℂ :=
  ∑ j, radianAction (directionProjectionEntry i j) (w j) x

/-- The complementary vector projection on the same Schwartz input. -/
def hodgeLongitudinalAction (w : HodgeSchwartzField) (i : Fin 4) (x : E) : ℂ :=
  w i x - hodgeTransverseAction w i x

private def hodgePhase (x ξ : E) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)

private theorem integrable_hodgePhase_mul {s : E → ℂ} (hs : Integrable s) (x : E) :
    Integrable (fun ν => hodgePhase x ν * s ν) := by
  have hc : Continuous (hodgePhase x) := by unfold hodgePhase; fun_prop
  exact hs.bdd_mul hc.aestronglyMeasurable ⟨1, fun ν => by simp [hodgePhase, Complex.norm_exp]⟩

private theorem inverse_add {s t : E → ℂ} (hs : Integrable s) (ht : Integrable t) :
    𝓕⁻ (s + t) = 𝓕⁻ s + 𝓕⁻ t := by
  funext x
  simp only [Real.fourierIntegralInv_eq', Pi.add_apply, smul_eq_mul, mul_add]
  exact integral_add (integrable_hodgePhase_mul hs x) (integrable_hodgePhase_mul ht x)

private theorem inverse_sub {s t : E → ℂ} (hs : Integrable s) (ht : Integrable t) :
    𝓕⁻ (s - t) = 𝓕⁻ s - 𝓕⁻ t := by
  funext x
  simp only [Real.fourierIntegralInv_eq', Pi.sub_apply, smul_eq_mul, mul_sub]
  exact integral_sub (integrable_hodgePhase_mul hs x) (integrable_hodgePhase_mul ht x)

private theorem inverse_neg (s : E → ℂ) : 𝓕⁻ (-s) = -𝓕⁻ s := by
  funext x
  simp only [Real.fourierIntegralInv_eq', Pi.neg_apply, smul_eq_mul, mul_neg, integral_neg]

private def hodgeStdSpectrum (w : HodgeSchwartzField) (i : Fin 4) : E → ℂ :=
  fun ν => hodgeSpectrum w (tau • ν) i

private def hodgeStdTransverse (w : HodgeSchwartzField) (i : Fin 4) : E → ℂ :=
  fun ν => hodgeTransverse (tau • ν) (hodgeSpectrum w (tau • ν)) i

private theorem hodgeStdSpectrum_eq (w : HodgeSchwartzField) (i : Fin 4) :
    hodgeStdSpectrum w i = (SchwartzMap.fourierTransformCLM ℂ (w i) : E → ℂ) := by
  funext ν
  exact radianFourier_scaled (w i) ν

private theorem hodgeStdSpectrum_integrable (w : HodgeSchwartzField) (i : Fin 4) :
    Integrable (hodgeStdSpectrum w i) := by
  rw [hodgeStdSpectrum_eq]
  exact (SchwartzMap.fourierTransformCLM ℂ (w i)).integrable

private theorem inverse_hodgeStdSpectrum (w : HodgeSchwartzField) (i : Fin 4) :
    𝓕⁻ (hodgeStdSpectrum w i) = (w i : E → ℂ) := by
  rw [hodgeStdSpectrum_eq]
  exact (w i).continuous.fourier_inversion (w i).integrable
    (SchwartzMap.fourierTransformCLM ℂ (w i)).integrable

private theorem hodgeStdTransverse_eq (w : HodgeSchwartzField) (i : Fin 4) :
    hodgeStdTransverse w i = ∑ j, radianActionSpectrum (directionProjectionEntry i j) (w j) := by
  funext ν
  simp only [hodgeStdTransverse, hodgeTransverse_apply, Finset.sum_apply, radianActionSpectrum,
    hodgeSpectrum, radianFourier_scaled]

private theorem hodgeEntrySpectrum_integrable (w : HodgeSchwartzField) (i j : Fin 4) :
    Integrable (radianActionSpectrum (directionProjectionEntry i j) (w j)) :=
  (radianActionSpectrum_degreeZero_data _ (directionProjectionEntry_contDiffOn i j)
    (directionProjectionEntry_scale i j) (w j)).2.1

private theorem hodgeStdTransverse_integrable (w : HodgeSchwartzField) (i : Fin 4) :
    Integrable (hodgeStdTransverse w i) := by
  rw [hodgeStdTransverse_eq]
  simpa only [Finset.sum_apply] using
    (integrable_finset_sum Finset.univ (fun j _ => hodgeEntrySpectrum_integrable w i j))

private theorem inverse_hodgeStdTransverse (w : HodgeSchwartzField) (i : Fin 4) :
    𝓕⁻ (hodgeStdTransverse w i) = hodgeTransverseAction w i := by
  funext x
  rw [hodgeStdTransverse_eq]
  unfold hodgeTransverseAction
  simp_rw [← radianActionSpectrum_inverse]
  simp_rw [Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ν, hodgePhase x ν * (∑ j, radianActionSpectrum (directionProjectionEntry i j) (w j)) ν) =
    ∑ j, ∫ ν, hodgePhase x ν * radianActionSpectrum (directionProjectionEntry i j) (w j) ν
  rw [← integral_finset_sum _ (fun j _ => integrable_hodgePhase_mul (hodgeEntrySpectrum_integrable w i j) x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by simp only [Finset.sum_apply, Finset.mul_sum])

/-- The same symbol on a Schwartz Hodge pair identifies the physical projection. -/
theorem hodgeTransverseAction_eq_of_spectrum (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) (i : Fin 4) :
    hodgeTransverseAction w i = (A i : E → ℂ) := by
  rw [← inverse_hodgeStdTransverse, show hodgeStdTransverse w i = hodgeStdSpectrum A i from
    funext (fun ν => (congrFun (hA (tau • ν)) i).symm), inverse_hodgeStdSpectrum]

private theorem hodgeSpectrum_derivative (b : Fin 4) (w : HodgeSchwartzField) (ξ : E) :
    hodgeSpectrum (fun i => coordinateDerivative b (w i)) ξ =
      (Complex.I * (ξ b : ℂ)) • hodgeSpectrum w ξ := by
  ext i
  simp only [hodgeSpectrum, radianFourier_coordinateDerivative, Pi.smul_apply, smul_eq_mul]

/-- A coordinate derivative has the same transverse component differentiated in
that coordinate, on the domain of actual Schwartz Hodge pairs. -/
theorem hodgeTransverseAction_derivative (b : Fin 4) (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) (i : Fin 4) :
    hodgeTransverseAction (fun j => coordinateDerivative b (w j)) i =
      (coordinateDerivative b (A i) : E → ℂ) := by
  apply hodgeTransverseAction_eq_of_spectrum
  intro ξ
  rw [hodgeSpectrum_derivative, hodgeSpectrum_derivative, hA, map_smul]

/-- Physical differentiated commutator for the one-slot projection appearing
in the paper, as the sum of two actual multiplier actions on first derivatives of f. -/
theorem hodgeCommutator_action (b : Fin 4) (f : SchwartzMap E ℂ) (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ))
    (i : Fin 4) (x : E) :
    hodgeTransverseAction (fun j => hodgeProduct f (coordinateDerivative b (w j))) i x -
      f x * hodgeTransverseAction (fun j => coordinateDerivative b (w j)) i x =
    -hodgeTransverseAction (fun j => hodgeProduct (coordinateDerivative j f) ((w - A) b)) i x +
      hodgeLongitudinalAction (fun j => ∑ k, hodgeProduct (coordinateDerivative k f)
        (hodgeSkew b A k j)) i x := by
  rw [hodgeTransverseAction_derivative b w A hA]
  let fw : HodgeSchwartzField := fun j => hodgeProduct f (coordinateDerivative b (w j))
  let fA : HodgeSchwartzField := fun j => hodgeProduct f (coordinateDerivative b (A j))
  let grad : HodgeSchwartzField := fun j => hodgeProduct (coordinateDerivative j f) ((w - A) b)
  let skew : HodgeSchwartzField := fun j => ∑ k, hodgeProduct (coordinateDerivative k f) (hodgeSkew b A k j)
  have eq : hodgeStdTransverse fw i - hodgeStdSpectrum fA i =
      -hodgeStdTransverse grad i + (hodgeStdSpectrum skew i - hodgeStdTransverse skew i) := by
    funext ν
    exact congrFun (hodgeCommutator_spectrum b f w A hA (tau • ν)) i
  have heq := congrArg (fun s : E → ℂ => 𝓕⁻ s x) eq
  change 𝓕⁻ (hodgeStdTransverse fw i - hodgeStdSpectrum fA i) x =
    𝓕⁻ (-hodgeStdTransverse grad i + (hodgeStdSpectrum skew i - hodgeStdTransverse skew i)) x at heq
  have hP := hodgeStdTransverse_integrable fw i
  have hA' := hodgeStdSpectrum_integrable fA i
  have hg := hodgeStdTransverse_integrable grad i
  have hs := hodgeStdSpectrum_integrable skew i
  have ht := hodgeStdTransverse_integrable skew i
  rw [inverse_sub hP hA', inverse_add hg.neg (hs.sub ht), inverse_neg, inverse_sub hs ht,
    inverse_hodgeStdSpectrum, inverse_hodgeStdSpectrum, inverse_hodgeStdTransverse,
    inverse_hodgeStdTransverse, inverse_hodgeStdTransverse] at heq
  exact heq

end Burnett.P01
