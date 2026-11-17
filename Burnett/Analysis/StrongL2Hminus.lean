import Burnett.Analysis.Sobolev.Pairing
import Burnett.Analysis.Sobolev.L2Bounds
import Burnett.Analysis.IBP.CompactIBP

/-!
# StrongL2Hminus

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.Analysis.HminusStrongL2

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing

abbrev Hminus := Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ

def valueCoefficients (u : ScalarL2) : JetSpace := coefficients u (fun _ => 0)

def directionalCoefficients (v : Space) (u : ScalarL2) : JetSpace :=
  coefficients 0 (fun i => v i • u)

def valueFunctional (u : ScalarL2) : Hminus :=
  Burnett.X02.GraphDual.coefficientFunctional J (valueCoefficients u)

def directionalFunctional (v : Space) (u : ScalarL2) : Hminus :=
  Burnett.X02.GraphDual.coefficientFunctional J (directionalCoefficients v u)

theorem norm_valueCoefficients (u : ScalarL2) : ‖valueCoefficients u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp [valueCoefficients, coefficients, Fin.sum_univ_succ]

theorem norm_directionalCoefficients (v : Space) (u : ScalarL2) :
    ‖directionalCoefficients v u‖ = ‖v‖ * ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  simp [directionalCoefficients, coefficients, Fin.sum_univ_succ, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_valueFunctional_le (u : ScalarL2) : ‖valueFunctional u‖ ≤ ‖u‖ :=
  (Burnett.X02.GraphDual.norm_coefficientFunctional_le J _).trans_eq (norm_valueCoefficients u)

theorem norm_directionalFunctional_le (v : Space) (u : ScalarL2) :
    ‖directionalFunctional v u‖ ≤ ‖v‖ * ‖u‖ :=
  (Burnett.X02.GraphDual.norm_coefficientFunctional_le J _).trans_eq
    (norm_directionalCoefficients v u)

theorem directional_basis_expansion (φ : Space → ℝ) (v x : Space) :
    fderiv ℝ φ x v = ∑ i : Fin 4, v i * directional i φ x := by
  have hv : v = ∑ i : Fin 4, v i • EuclideanSpace.single i 1 := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_succ, PiLp.add_apply, PiLp.smul_apply,
      EuclideanSpace.single_apply]
  calc
    fderiv ℝ φ x v = fderiv ℝ φ x (∑ i : Fin 4, v i • EuclideanSpace.single i 1) :=
      congrArg (fderiv ℝ φ x) hv
    _ = ∑ i : Fin 4, v i * directional i φ x := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_smul, smul_eq_mul, directional]

theorem valueFunctional_test {f : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space))
    (φ : D) :
    valueFunctional (hf.toLp f) (Burnett.X02.GraphDual.testMap J φ) =
      ∫ x, f x * (φ : Space → ℝ) x := by
  have h := coefficientFunctional_test_of_memLp f (fun _ : Fin 4 => (0 : Space → ℝ))
    hf (fun _ => MemLp.zero) φ
  simpa only [MemLp.toLp_zero, Pi.zero_apply, zero_mul, integral_zero,
    Finset.sum_const_zero, sub_zero, valueFunctional, valueCoefficients] using h

theorem directionalFunctional_test {f : Space → ℝ}
    (hf : MemLp f 2 (volume : Measure Space)) (v : Space) (φ : D) :
    directionalFunctional v (hf.toLp f) (Burnett.X02.GraphDual.testMap J φ) =
      -(∫ x, f x * fderiv ℝ (φ : Space → ℝ) x v) := by
  have h := coefficientFunctional_test_of_memLp (fun _ : Space => (0 : ℝ))
    (fun i x => v i * f x) MemLp.zero (fun i => hf.const_mul (v i)) φ
  have hi (i : Fin 4) : Integrable
      (fun x => v i * (f x * directional i (φ : Space → ℝ) x)) :=
    (integrable_directional_product_of_memLp f hf i φ).const_mul (v i)
  have hV (i : Fin 4) : (hf.const_mul (v i)).toLp (fun x => v i * f x) = v i • hf.toLp f := by
    exact MemLp.toLp_const_smul (v i) hf
  simp only [zero_mul, integral_zero, zero_sub] at h
  simp_rw [hV] at h
  change directionalFunctional v (hf.toLp f) (Burnett.X02.GraphDual.testMap J φ) = _ at h
  rw [h]
  simp_rw [mul_assoc]
  rw [← integral_finset_sum _ (fun i _ => hi i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [directional_basis_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directionalFunctional_test_of_smooth {f : Space → ℝ}
    (hf : MemLp f 2 (volume : Measure Space)) (hfs : ContDiff ℝ ∞ f)
    (v : Space) (φ : D) :
    directionalFunctional v (hf.toLp f) (Burnett.X02.GraphDual.testMap J φ) =
      ∫ x, (φ : Space → ℝ) x * fderiv ℝ f x v := by
  rw [directionalFunctional_test]
  symm
  simpa only [mul_comm] using Burnett.X02.CompactIBP.integral_test_directional
    (test_smooth φ) (test_compactSupport φ) hfs v

theorem valueFunctional_test_bound (u : ScalarL2) (φ : D) :
    |valueFunctional u (Burnett.X02.GraphDual.testMap J φ)| ≤ ‖u‖ * ‖J φ‖ := by
  have h := (valueFunctional u).le_opNorm (Burnett.X02.GraphDual.testMap J φ)
  change ‖valueFunctional u (Burnett.X02.GraphDual.testMap J φ)‖ ≤ ‖valueFunctional u‖ * ‖J φ‖ at h
  simpa only [Real.norm_eq_abs] using h.trans
    (mul_le_mul_of_nonneg_right (norm_valueFunctional_le u) (norm_nonneg _))

theorem directionalFunctional_test_bound (v : Space) (u : ScalarL2) (φ : D) :
    |directionalFunctional v u (Burnett.X02.GraphDual.testMap J φ)| ≤
      (‖v‖ * ‖u‖) * ‖J φ‖ := by
  have h := (directionalFunctional v u).le_opNorm (Burnett.X02.GraphDual.testMap J φ)
  change ‖directionalFunctional v u (Burnett.X02.GraphDual.testMap J φ)‖ ≤
    ‖directionalFunctional v u‖ * ‖J φ‖ at h
  simpa only [Real.norm_eq_abs] using h.trans
    (mul_le_mul_of_nonneg_right (norm_directionalFunctional_le v u) (norm_nonneg _))

theorem valueFunctional_tendsto_zero {ι : Type*} {l : Filter ι} {u : ι → ScalarL2}
    (hu : Tendsto u l (𝓝 0)) : Tendsto (fun n => valueFunctional (u n)) l (𝓝 0) := by
  apply (Metric.tendsto_nhds (u := fun n => valueFunctional (u n)) (a := (0 : Hminus))).mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hu) ε hε] with n hn
  rw [dist_zero_right] at hn
  rw [dist_zero_right (valueFunctional (u n))]
  exact (norm_valueFunctional_le (u n)).trans_lt hn

theorem directionalFunctional_tendsto_zero {ι : Type*} {l : Filter ι} {u : ι → ScalarL2}
    (hu : Tendsto u l (𝓝 0)) (v : Space) :
    Tendsto (fun n => directionalFunctional v (u n)) l (𝓝 0) := by
  have hn : Tendsto (fun n => ‖u n‖) l (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ScalarL2)).comp hu
  have hb : Tendsto (fun n => ‖v‖ * ‖u n‖) l (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul ‖v‖
  apply (Metric.tendsto_nhds (u := fun n => directionalFunctional v (u n)) (a := (0 : Hminus))).mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hb) ε hε] with n hn
  rw [dist_zero_right] at hn
  rw [dist_zero_right (directionalFunctional v (u n))]
  have hnonneg := mul_nonneg (norm_nonneg v) (norm_nonneg (u n))
  have hsmall : ‖v‖ * ‖u n‖ < ε := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hn
  exact (norm_directionalFunctional_le v (u n)).trans_lt hsmall

theorem smooth_strongL2_directional_realization {ι : Type*} {l : Filter ι}
    (f : ι → Space → ℝ) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hu : Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 0)) (v : Space) :
    ∃ F : ι → Hminus,
      (∀ n (φ : D), F n (Burnett.X02.GraphDual.testMap J φ) =
        ∫ x, (φ : Space → ℝ) x * fderiv ℝ (f n) x v) ∧
      Tendsto F l (𝓝 0) := by
  exact ⟨fun n => directionalFunctional v ((hf n).toLp (f n)),
    fun n φ => directionalFunctional_test_of_smooth (hf n) (hs n) v φ,
    directionalFunctional_tendsto_zero hu v⟩

end Burnett.Analysis.HminusStrongL2
