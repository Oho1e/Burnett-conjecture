import Burnett.Analysis.Cubic.Distribution
import Burnett.Analysis.Cubic.LocalHminus
import Burnett.Analysis.Sobolev.NonzeroTest

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace Burnett.CubicCounterexample

open CubicExplicit

abbrev Test := X02.SobolevTestJet.D
abbrev Hminus1 := X02.GraphDual.Graph X02.SobolevTestJet.J →L[ℝ] ℝ

/-- Strong local negative Sobolev convergence in the standard completed-test
H¹ model: each fixed compact smooth localization has its actual integral
represented by continuous dual elements converging in operator norm. -/
def StrongHminusLocalZero (T : ℕ → Space → ℝ) : Prop :=
  (∀ n, LocallyIntegrable (T n) (volume : Measure Space)) ∧
  ∀ χ : Test, ∃ L : ℕ → Hminus1, Tendsto L atTop (𝓝 0) ∧
    ∀ (n : ℕ) (φ : Test),
      L n (X02.GraphDual.testMap X02.SobolevTestJet.J φ) =
        ∫ x : Space, (χ : Space → ℝ) x * T n x * (φ : Space → ℝ) x

theorem f_wave_strongHminusLocalZero :
    StrongHminusLocalZero (fun n => waveOperator (fSequence n)) := by
  constructor
  · intro n
    change LocallyIntegrable (waveOperator (fSequence n)) (volume : Measure Space)
    have hfun : waveOperator (fSequence n) =
        (fun x => 4 * N n * Real.sin (N n * v x) * Real.cos ((N n)^2 * u x)) :=
      funext (waveOperator_waveF ((N n)^2) (N n) (pow_ne_zero 2 (N_ne_zero n)))
    rw [hfun]
    have hs : ContDiff ℝ ∞ (fun x : Space =>
        4 * N n * Real.sin (N n * v x) * Real.cos ((N n)^2 * u x)) := by fun_prop
    exact hs.continuous.locallyIntegrable
  intro χ
  exact ⟨X02.LocalHminus.sourceFunctional χ,
    X02.LocalHminus.sourceFunctional_tendsto_zero χ,
    X02.LocalHminus.sourceFunctional_test χ⟩

theorem w_wave_strongHminusLocalZero :
    StrongHminusLocalZero (fun n => waveOperator (wSequence n)) := by
  constructor
  · intro n
    change LocallyIntegrable (waveOperator (wSequence n)) (volume : Measure Space)
    have hfun : waveOperator (wSequence n) = (fun _ => 0) :=
      funext (waveOperator_waveW (N n) (N_ne_zero n))
    rw [hfun]
    exact continuous_const.locallyIntegrable
  intro χ
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
  intro n φ
  simp [wSequence, waveOperator_waveW _ (N_ne_zero n)]

/-- The manuscript's proposition prop:cubic, with one common pair of
sequences for all conclusions. Uniform convergence is proved globally. The
extra off-null conic-projection assertion in its proof is not an output. -/
theorem auxiliary_trilinear_counterexample :
    ∃ f w : ℕ → Space → ℝ,
      (∀ n, ContDiff ℝ ∞ (f n) ∧ ContDiff ℝ ∞ (w n)) ∧
      TendstoUniformly f (fun _ => 0) atTop ∧
      TendstoUniformly w (fun _ => 0) atTop ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (i : Fin 4) (x : Space),
        |D i (f n) x| ≤ C ∧ |D i (w n) x| ≤ C) ∧
      StrongHminusLocalZero (fun n => waveOperator (f n)) ∧
      StrongHminusLocalZero (fun n => waveOperator (w n)) ∧
      (∀ (φ : Test) (n : ℕ), Integrable (fun x : Space => (φ : Space → ℝ) x *
        (nullForm (f n) (w n) x * D 0 (f n) x))) ∧
      (∀ φ : Test, Tendsto (fun n => ∫ x : Space, (φ : Space → ℝ) x *
        (nullForm (f n) (w n) x * D 0 (f n) x)) atTop
        (𝓝 ((-(1/4) : ℝ) * (∫ x : Space, (φ : Space → ℝ) x)))) := by
  refine ⟨fSequence, wSequence, ?_, CubicFrequencies.tendstoUniformly_fSequence,
    CubicFrequencies.tendstoUniformly_wSequence, ?_, f_wave_strongHminusLocalZero,
    w_wave_strongHminusLocalZero, CubicDistribution.cubic_integrable,
    CubicDistribution.cubic_integral_tendsto⟩
  · intro n
    exact ⟨fSequence_smooth n, wSequence_smooth n⟩
  · refine ⟨2, by norm_num, ?_⟩
    intro n i x
    exact ⟨D_fSequence_abs_le_two n i x,
      (D_wSequence_abs_le_one n i x).trans (by norm_num)⟩

theorem cubic_unitTest_tendsto_neg_quarter :
    Tendsto (fun n => ∫ x : Space, (X02.NonzeroTest.unitTest : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x))
      atTop (𝓝 (-(1/4) : ℝ)) := by
  simpa only [X02.NonzeroTest.unitTest_integral, mul_one] using
    CubicDistribution.cubic_integral_tendsto X02.NonzeroTest.unitTest

theorem cubic_unitTest_not_tendsto_zero :
    ¬ Tendsto (fun n => ∫ x : Space, (X02.NonzeroTest.unitTest : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x))
      atTop (𝓝 (0 : ℝ)) := by
  intro hzero
  have heq : (0 : ℝ) = -(1/4) := tendsto_nhds_unique hzero cubic_unitTest_tendsto_neg_quarter
  norm_num at heq

#print axioms auxiliary_trilinear_counterexample
#print axioms cubic_unitTest_not_tendsto_zero

end Burnett.CubicCounterexample
