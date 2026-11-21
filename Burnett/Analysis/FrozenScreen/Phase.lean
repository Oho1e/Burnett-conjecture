import Burnett.Analysis.FrozenScreen.Projection
import Burnett.Algebra.ComplexPolarization
import Burnett.Analysis.TransportWard.MetricVariation

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open scoped Matrix BigOperators

/-- Raise both indices of a complex covariant tensor with the real inverse metric. -/
def raiseBoth (B : ScreenMatrix) (J : ComplexTensor2) (a b : Index) : ℂ :=
  ∑ c, (B a c : ℂ) * complexRaiseSecond B J c b

/-- The density-weighted trace reversal of the Fourier Ricci symbol, in the
lower-component variational convention of the paper. -/
def einsteinDensitySymbol (B : ScreenMatrix) (w : ℝ) (q : Covector)
    (J : ComplexTensor2) (a b : Index) : ℂ :=
  (w : ℂ) * (raiseBoth B (complexRicciSymbol B q J) a b -
    (B a b : ℂ) * complexMetricTrace B (complexRicciSymbol B q J) / 2)

/-- The map associated to the frozen physical coefficient C. -/
def physicalCoefficient (B : ScreenMatrix) (J : ComplexTensor2) (a b : Index) : ℂ :=
  (raiseBoth B J a b - (B a b : ℂ) * complexMetricTrace B J / 2) / 4

private theorem screen_ricci_eq (B : ScreenMatrix) (q : Covector) (J : ComplexTensor2)
    (ht : complexMetricTrace B J = 0) (hq : ∀ i, complexContracted B q J i = 0) :
    complexRicciSymbol B q J = ((symbolNorm B q : ℂ) / 2) • J := by
  funext i j
  simp only [complexRicciSymbol, ht, hq, mul_zero, add_zero, sub_zero, Pi.smul_apply, smul_eq_mul]
  ring

private theorem complexMetricTrace_smul_slot (B : ScreenMatrix) (c : ℂ) (J : ComplexTensor2) :
    complexMetricTrace B (c • J) = c * complexMetricTrace B J := by
  simp only [complexMetricTrace, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem raiseBoth_smul (B : ScreenMatrix) (c : ℂ) (J : ComplexTensor2)
    (a b : Index) : raiseBoth B (c • J) a b = c * raiseBoth B J a b := by
  simp only [raiseBoth, complexRaiseSecond, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two screen contractions suffice for the exact phase extraction,
including off the null cone and with the full weight and both raised indices. -/
theorem einsteinDensitySymbol_screen_phase
    (B : ScreenMatrix) (w : ℝ) (q : Covector) (J : ComplexTensor2)
    (ht : complexMetricTrace B J = 0) (hq : ∀ i, complexContracted B q J i = 0)
    (a b : Index) :
    einsteinDensitySymbol B w q J a b =
      (w : ℂ) * (symbolNorm B q : ℂ) / 2 * raiseBoth B J a b ∧
    einsteinDensitySymbol B w q J a b =
      2 * (w : ℂ) * (symbolNorm B q : ℂ) * physicalCoefficient B J a b := by
  simp only [einsteinDensitySymbol, screen_ricci_eq B q J ht hq, raiseBoth_smul,
    complexMetricTrace_smul_slot, ht, mul_zero, zero_div, sub_zero, physicalCoefficient]
  constructor <;> ring

/-- The same equality for the actual frozen metric, with w = sqrt(|det m|). -/
theorem frozenEinsteinSymbol_screen_phase
    (m : ScreenMatrix) (q : Covector) (J : ComplexTensor2)
    (ht : complexMetricTrace (inverseMatrix m) J = 0)
    (hq : ∀ i, complexContracted (inverseMatrix m) q J i = 0) (a b : Index) :
    let B := inverseMatrix m
    let w := metricDensity m
    einsteinDensitySymbol B w q J a b =
      (w : ℂ) * (symbolNorm B q : ℂ) / 2 * raiseBoth B J a b ∧
    einsteinDensitySymbol B w q J a b =
      2 * (w : ℂ) * (symbolNorm B q : ℂ) * physicalCoefficient B J a b :=
  einsteinDensitySymbol_screen_phase (inverseMatrix m) (metricDensity m) q J ht hq a b

end Burnett.V06
