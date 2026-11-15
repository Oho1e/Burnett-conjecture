import Burnett.Analysis.Sobolev.Pairing
import Burnett.Analysis.Sobolev.L2Bounds
import Burnett.Analysis.IBP.LocalizedIBP
import Burnett.Analysis.Cubic.FrequencyBounds

/- Tree-external assembly of the actual localized wave source in the dual
of the closed graph of the genuine C∞c first jet.  All L² objects below have
MemLp witnesses; test evaluation uses the proved compact-support IBP formula. -/
noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Burnett.X02.LocalHminus

open SobolevTestJet TestJetPairing
open Burnett.CubicExplicit Burnett.CubicFrequencies

abbrev Test := SobolevTestJet.D
abbrev Space := SobolevTestJet.Space

def flux (n : ℕ) (i : Fin 4) : Space → ℝ :=
  fluxComponent ((N n)^2) (N n) i

theorem flux_smooth (n : ℕ) (i : Fin 4) : ContDiff ℝ ∞ (flux n i) := by
  have hs : ContDiff ℝ ∞ (sinSin ((N n)^2) (N n)) :=
    (((N n) • v).contDiff.sin).mul ((((N n)^2) • u).contDiff.sin)
  exact contDiff_const.mul (contDiff_const.mul hs)

theorem flux_abs_le (n : ℕ) (i : Fin 4) (x : Space) :
    |flux n i x| ≤ (2 * (N n)⁻¹) := by
  have h := fluxComponent_abs_le ((N n)^2) (N n) i x
  rwa [N_ratio, abs_of_pos (inv_pos.mpr (N_pos n))] at h

def localizedFlux (χ : Test) (n : ℕ) (i : Fin 4) (x : Space) : ℝ :=
  (χ : Space → ℝ) x * flux n i x

def lowerSource (χ : Test) (n : ℕ) (x : Space) : ℝ :=
  -(∑ i : Fin 4, directional i (χ : Space → ℝ) x * flux n i x)

def gradientMajorant (χ : Test) (x : Space) : ℝ :=
  ∑ i : Fin 4, |directional i (χ : Space → ℝ) x|

theorem gradientMajorant_nonneg (χ : Test) (x : Space) : 0 ≤ gradientMajorant χ x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem localizedFlux_memLp (χ : Test) (n : ℕ) (i : Fin 4) :
    MemLp (localizedFlux χ n i) 2 (volume : Measure Space) :=
  ((test_smooth χ).continuous.mul (flux_smooth n i).continuous).memLp_of_hasCompactSupport
    ((test_compactSupport χ).mul_right)

theorem lowerSource_memLp (χ : Test) (n : ℕ) :
    MemLp (lowerSource χ n) 2 (volume : Measure Space) := by
  apply MemLp.neg
  apply memLp_finset_sum Finset.univ
  intro i _
  exact ((directional_continuous i χ).mul (flux_smooth n i).continuous).memLp_of_hasCompactSupport
    ((directional_compactSupport i χ).mul_right)

theorem gradientMajorant_memLp (χ : Test) :
    MemLp (gradientMajorant χ) 2 (volume : Measure Space) := by
  apply memLp_finset_sum Finset.univ
  intro i _
  simpa only [Real.norm_eq_abs] using (directional_memLp i χ).norm

theorem localizedFlux_abs_le (χ : Test) (n : ℕ) (i : Fin 4) (x : Space) :
    |localizedFlux χ n i x| ≤ (2 * (N n)⁻¹) * |(χ : Space → ℝ) x| := by
  rw [localizedFlux, abs_mul]
  calc
    _ ≤ |(χ : Space → ℝ) x| * (2 * (N n)⁻¹) :=
      mul_le_mul_of_nonneg_left (flux_abs_le n i x) (abs_nonneg _)
    _ = _ := mul_comm _ _

theorem lowerSource_abs_le (χ : Test) (n : ℕ) (x : Space) :
    |lowerSource χ n x| ≤ (2 * (N n)⁻¹) * |gradientMajorant χ x| := by
  rw [lowerSource, abs_neg, abs_of_nonneg (gradientMajorant_nonneg χ x)]
  calc
    _ ≤ ∑ i : Fin 4, |directional i (χ : Space → ℝ) x * flux n i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, (2 * (N n)⁻¹) * |directional i (χ : Space → ℝ) x| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      calc
        _ ≤ |directional i (χ : Space → ℝ) x| * (2 * (N n)⁻¹) :=
          mul_le_mul_of_nonneg_left (flux_abs_le n i x) (abs_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem decay_nonneg (n : ℕ) : 0 ≤ 2 * (N n)⁻¹ :=
  mul_nonneg (by norm_num) (inv_nonneg.mpr (N_pos n).le)

theorem decay_tendsto_zero : Tendsto (fun n => 2 * (N n)⁻¹) atTop (𝓝 0) := by
  simpa only [mul_zero] using tendsto_inv_N_zero.const_mul 2

def localizedFluxLp (χ : Test) (n : ℕ) (i : Fin 4) : ScalarL2 :=
  (localizedFlux_memLp χ n i).toLp (localizedFlux χ n i)

def lowerSourceLp (χ : Test) (n : ℕ) : ScalarL2 :=
  (lowerSource_memLp χ n).toLp (lowerSource χ n)

theorem localizedFluxLp_tendsto_zero (χ : Test) (i : Fin 4) :
    Tendsto (fun n => localizedFluxLp χ n i) atTop (𝓝 0) :=
  L2Bounds.toLp_tendsto_zero_of_bound (fun n => localizedFlux_memLp χ n i)
    (test_memLp χ) decay_nonneg decay_tendsto_zero (fun n x => localizedFlux_abs_le χ n i x)

theorem lowerSourceLp_tendsto_zero (χ : Test) :
    Tendsto (lowerSourceLp χ) atTop (𝓝 0) :=
  L2Bounds.toLp_tendsto_zero_of_bound (lowerSource_memLp χ)
    (gradientMajorant_memLp χ) decay_nonneg decay_tendsto_zero (lowerSource_abs_le χ)

def coefficientSequence (χ : Test) (n : ℕ) : JetSpace :=
  coefficients (lowerSourceLp χ n) (localizedFluxLp χ n)

theorem coefficientSequence_tendsto_zero (χ : Test) :
    Tendsto (coefficientSequence χ) atTop (𝓝 0) := by
  have hpi : Tendsto
      (fun n => Fin.cases (lowerSourceLp χ n) (fun i => -localizedFluxLp χ n i))
      atTop (𝓝 (fun _ : Fin 5 => (0 : ScalarL2))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact lowerSourceLp_tendsto_zero χ
    · simpa only [neg_zero] using (localizedFluxLp_tendsto_zero χ i).neg
  change Tendsto
    (fun n => WithLp.toLp 2 (Fin.cases (lowerSourceLp χ n) (fun i => -localizedFluxLp χ n i)))
    atTop (𝓝 (WithLp.toLp 2 (fun _ : Fin 5 => (0 : ScalarL2))))
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 5 => ScalarL2)).tendsto _).comp hpi

def smallFunctional (χ : Test) (n : ℕ) : GraphDual.Graph J →L[ℝ] ℝ :=
  GraphDual.coefficientFunctional J (coefficientSequence χ n)

theorem smallFunctional_tendsto_zero (χ : Test) :
    Tendsto (smallFunctional χ) atTop (𝓝 0) :=
  GraphDual.coefficientFunctional_tendsto_zero J (coefficientSequence_tendsto_zero χ)

theorem smallFunctional_test (χ : Test) (n : ℕ) (φ : Test) :
    smallFunctional χ n (GraphDual.testMap J φ) =
      ∫ x : Space, (χ : Space → ℝ) x * waveOperator (fSequence n) x *
        (φ : Space → ℝ) x := by
  calc
    _ = (∫ x : Space, lowerSource χ n x * (φ : Space → ℝ) x) -
        ∑ i : Fin 4, ∫ x : Space,
          localizedFlux χ n i x * directional i (φ : Space → ℝ) x :=
      coefficientFunctional_test_of_memLp (lowerSource χ n) (localizedFlux χ n)
        (lowerSource_memLp χ n) (localizedFlux_memLp χ n) φ
    _ = _ := by
      symm
      have heq (x : Space) : waveOperator (fSequence n) x =
          ∑ i : Fin 4, fderiv ℝ (flux n i) x (EuclideanSpace.single i 1) := by
        exact waveOperator_waveF_eq_divergence ((N n)^2) (N n)
          (pow_ne_zero 2 (N_ne_zero n)) x
      simp_rw [heq]
      exact LocalizedIBP.integral_localized_divergence (test_smooth χ) (test_compactSupport χ)
        (test_smooth φ) (flux_smooth n)

def localizedWaveSource (χ : Test) (n : ℕ) (x : Space) : ℝ :=
  (χ : Space → ℝ) x * waveOperator (fSequence n) x

theorem waveSource_continuous (n : ℕ) : Continuous (waveOperator (fSequence n)) := by
  have heq : waveOperator (fSequence n) =
      fun x : Space => 4 * N n * Real.sin (N n * v x) * Real.cos ((N n)^2 * u x) := by
    funext x
    exact waveOperator_waveF ((N n)^2) (N n) (pow_ne_zero 2 (N_ne_zero n)) x
  rw [heq]
  have hs : ContDiff ℝ ∞ (fun x : Space => Real.sin (N n * v x)) :=
    ((N n) • v).contDiff.sin
  have hc : ContDiff ℝ ∞ (fun x : Space => Real.cos ((N n)^2 * u x)) :=
    (((N n)^2) • u).contDiff.cos
  exact ((contDiff_const.mul hs).mul hc).continuous

theorem localizedWaveSource_memLp (χ : Test) (n : ℕ) :
    MemLp (localizedWaveSource χ n) 2 (volume : Measure Space) :=
  ((test_smooth χ).continuous.mul (waveSource_continuous n)).memLp_of_hasCompactSupport
    ((test_compactSupport χ).mul_right)

theorem localizedWaveSource_test_integrable (χ : Test) (n : ℕ) (φ : Test) :
    Integrable (fun x : Space => localizedWaveSource χ n x * (φ : Space → ℝ) x) volume :=
  integrable_value_product_of_memLp _ (localizedWaveSource_memLp χ n) φ

/-- The actual localized L² source, acting on the value coordinate of H¹. -/
def sourceFunctional (χ : Test) (n : ℕ) : GraphDual.Graph J →L[ℝ] ℝ :=
  GraphDual.coefficientFunctional J
    (coefficients ((localizedWaveSource_memLp χ n).toLp (localizedWaveSource χ n)) (fun _ => 0))

theorem sourceFunctional_test (χ : Test) (n : ℕ) (φ : Test) :
    sourceFunctional χ n (GraphDual.testMap J φ) =
      ∫ x : Space, (χ : Space → ℝ) x * waveOperator (fSequence n) x *
        (φ : Space → ℝ) x := by
  have h := coefficientFunctional_test_of_memLp (localizedWaveSource χ n)
    (fun _ : Fin 4 => (0 : Space → ℝ)) (localizedWaveSource_memLp χ n)
    (fun _ => MemLp.zero) φ
  simpa only [MemLp.toLp_zero, Pi.zero_apply, zero_mul, integral_zero,
    Finset.sum_const_zero, sub_zero, sourceFunctional, localizedWaveSource] using h

/-- Equality follows from actual IBP on a dense set of genuine smooth tests. -/
theorem sourceFunctional_eq_smallFunctional (χ : Test) (n : ℕ) :
    sourceFunctional χ n = smallFunctional χ n := by
  apply GraphDual.testRestriction_injective J
  ext φ
  change sourceFunctional χ n (GraphDual.testMap J φ) =
    smallFunctional χ n (GraphDual.testMap J φ)
  rw [sourceFunctional_test, smallFunctional_test]

/-- Strong convergence in the normed continuous dual of the actual first-jet
graph closure, for every C∞ compactly supported localization χ. -/
theorem sourceFunctional_tendsto_zero (χ : Test) :
    Tendsto (sourceFunctional χ) atTop (𝓝 0) := by
  have heq : sourceFunctional χ = smallFunctional χ :=
    funext (sourceFunctional_eq_smallFunctional χ)
  rw [heq]
  exact smallFunctional_tendsto_zero χ

set_option synthInstance.maxHeartbeats 200000 in
theorem norm_sourceFunctional_tendsto_zero (χ : Test) :
    Tendsto (fun n => ‖sourceFunctional χ n‖) atTop (𝓝 0) := by
  have hn : Continuous (fun F : GraphDual.Graph J →L[ℝ] ℝ => ‖F‖) :=
    @continuous_norm (GraphDual.Graph J →L[ℝ] ℝ) inferInstance
  have h := (hn.tendsto (0 : GraphDual.Graph J →L[ℝ] ℝ)).comp
    (sourceFunctional_tendsto_zero χ)
  simpa only [Function.comp_def, ContinuousLinearMap.opNorm_zero] using h

#print axioms localizedFluxLp_tendsto_zero
#print axioms lowerSourceLp_tendsto_zero
#print axioms coefficientSequence_tendsto_zero
#print axioms smallFunctional_tendsto_zero
#print axioms smallFunctional_test
#print axioms sourceFunctional_eq_smallFunctional
#print axioms sourceFunctional_tendsto_zero
#print axioms norm_sourceFunctional_tendsto_zero

end Burnett.X02.LocalHminus
