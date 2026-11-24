import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory

variable {X I J : Type*} [MeasurableSpace X] [Countable I] [Countable J]

/-- Equality of all complex entry measures identifies their two densities on
the sum of the original reference measures, with the corresponding
Radon–Nikodym weights. -/
theorem ae_eq_amplitudeDensities_on_sum
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : X → Matrix I J ℂ)
    (hA : ∀ i j, Integrable (fun x => A x i j) μ)
    (hB : ∀ i j, Integrable (fun x => B x i j) ν)
    (hset : ∀ i j (S : Set X), MeasurableSet S →
      (∫ x in S, A x i j ∂μ) = ∫ x in S, B x i j ∂ν) :
    (fun x => (μ.rnDeriv (μ + ν) x).toReal • A x)
      =ᵐ[μ + ν] fun x => (ν.rnDeriv (μ + ν) x).toReal • B x := by
  let γ := μ + ν
  have hμ : μ ≪ γ := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hν : ν ≪ γ := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hentry (i : I) (j : J) :
      (fun x => (μ.rnDeriv γ x).toReal • A x i j)
        =ᵐ[γ] fun x => (ν.rnDeriv γ x).toReal • B x i j := by
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    · exact fun _ _ _ => ((integrable_rnDeriv_smul_iff hμ).mpr (hA i j)).integrableOn
    · exact fun _ _ _ => ((integrable_rnDeriv_smul_iff hν).mpr (hB i j)).integrableOn
    · intro S hS _
      rw [setIntegral_rnDeriv_smul hμ hS, setIntegral_rnDeriv_smul hν hS]
      exact hset i j S hS
  exact (ae_all_iff.mpr fun i => ae_all_iff.mpr (hentry i)).mono fun _ hx =>
    Matrix.ext fun i j => hx i j

omit [Countable I] [Countable J] in
/-- An intrinsic real contraction gives the same positive control measure
from either chart representation. On that measure the corresponding normalized
matrix densities agree. -/
theorem normalization_agrees_on_common_control
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : X → Matrix I J ℂ) (trace : X → Matrix I J ℂ →ₗ[ℝ] ℝ)
    (hA : AEMeasurable (fun x => trace x (A x)) (μ + ν))
    (hB : AEMeasurable (fun x => trace x (B x)) (μ + ν))
    (hab : (fun x => (μ.rnDeriv (μ + ν) x).toReal • A x)
      =ᵐ[μ + ν] fun x => (ν.rnDeriv (μ + ν) x).toReal • B x) :
    let τ := μ.withDensity (fun x => ENNReal.ofReal (trace x (A x)))
    τ = ν.withDensity (fun x => ENNReal.ofReal (trace x (B x))) ∧
      (fun x => (trace x (A x))⁻¹ • A x) =ᵐ[τ] fun x => (trace x (B x))⁻¹ • B x := by
  intro τ
  let γ := μ + ν
  let u := μ.rnDeriv γ
  let v := ν.rnDeriv γ
  let a (x : X) := trace x (A x)
  let b (x : X) := trace x (B x)
  let d (x : X) := u x * ENNReal.ofReal (a x)
  let e (x : X) := v x * ENNReal.ofReal (b x)
  have hμ : μ ≪ γ := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hν : ν ≪ γ := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hu : Measurable u := Measure.measurable_rnDeriv _ _
  have hv : Measurable v := Measure.measurable_rnDeriv _ _
  have ha : AEMeasurable (fun x => ENNReal.ofReal (a x)) γ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hA
  have hb : AEMeasurable (fun x => ENNReal.ofReal (b x)) γ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hB
  have hτ : τ = γ.withDensity d := by
    calc
      τ = (γ.withDensity u).withDensity (fun x => ENNReal.ofReal (a x)) :=
        congrArg (fun m : Measure X => m.withDensity _) (Measure.withDensity_rnDeriv_eq μ γ hμ).symm
      _ = _ := (withDensity_mul₀ hu.aemeasurable ha).symm
  have hτ' : ν.withDensity (fun x => ENNReal.ofReal (b x)) = γ.withDensity e := by
    calc
      _ = (γ.withDensity v).withDensity (fun x => ENNReal.ofReal (b x)) :=
        congrArg (fun m : Measure X => m.withDensity _) (Measure.withDensity_rnDeriv_eq ν γ hν).symm
      _ = _ := (withDensity_mul₀ hv.aemeasurable hb).symm
  have hscalar : ∀ᵐ x ∂γ, (u x).toReal * a x = (v x).toReal * b x := by
    filter_upwards [hab] with x hx
    simpa only [map_smul, smul_eq_mul] using congrArg (trace x) hx
  have hd : d =ᵐ[γ] e := by
    filter_upwards [hscalar, Measure.rnDeriv_lt_top μ γ, Measure.rnDeriv_lt_top ν γ]
      with x hx hu' hv'
    change u x < ⊤ at hu'
    change v x < ⊤ at hv'
    change u x * ENNReal.ofReal (a x) = v x * ENNReal.ofReal (b x)
    rw [← ENNReal.ofReal_toReal hu'.ne, ← ENNReal.ofReal_toReal hv'.ne,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hx]
  refine ⟨hτ.trans ((withDensity_congr_ae hd).trans hτ'.symm), ?_⟩
  rw [hτ, Filter.EventuallyEq, ae_withDensity_iff' (hu.aemeasurable.mul ha)]
  filter_upwards [hab, hscalar, Measure.rnDeriv_lt_top μ γ] with x hx hs hu' hNe
  change u x < ⊤ at hu'
  change d x ≠ 0 at hNe
  have hProd : (u x).toReal * a x ≠ 0 := by
    intro he
    apply hNe
    change u x * ENNReal.ofReal (a x) = 0
    rw [← ENNReal.ofReal_toReal hu'.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, he, ENNReal.ofReal_zero]
  have hProd' : (v x).toReal * b x ≠ 0 := hs ▸ hProd
  change (u x).toReal • A x = (v x).toReal • B x at hx
  calc
    (a x)⁻¹ • A x = ((u x).toReal * a x)⁻¹ • ((u x).toReal • A x) := by
      rw [smul_smul]
      congr 1
      field_simp [left_ne_zero_of_mul hProd, right_ne_zero_of_mul hProd]
    _ = ((v x).toReal * b x)⁻¹ • ((v x).toReal • B x) := by rw [hs, hx]
    _ = (b x)⁻¹ • B x := by
      rw [smul_smul]
      congr 1
      field_simp [left_ne_zero_of_mul hProd', right_ne_zero_of_mul hProd']

end Burnett.Microlocal.Overlap
