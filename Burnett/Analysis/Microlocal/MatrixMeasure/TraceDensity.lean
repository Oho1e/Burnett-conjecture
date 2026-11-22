import Burnett.Analysis.Microlocal.MatrixMeasure.Representation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.MatrixTraceDensity

open private Burnett.Microlocal.MatrixMeasureAssembly.posSemidef_of_nonneg_real_quadratic from Burnett.Analysis.Microlocal.MatrixMeasure.Assembly

open MeasureTheory Set Burnett.Microlocal.MatrixPolarization Burnett.Microlocal.MatrixMeasureAssembly
open scoped MeasureTheory Matrix ComplexOrder

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
theorem traceMeasure_isFinite (ν : (ι → ℂ) → Measure X) (hν : ∀ v, IsFiniteMeasure (ν v)) :
    IsFiniteMeasure (traceMeasure ν) := by
  unfold traceMeasure
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    infer_instance
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    letI : IsFiniteMeasure (ν (Pi.single i 1)) := hν _
    letI : IsFiniteMeasure (∑ j ∈ s, ν (Pi.single j 1)) := ih
    infer_instance

/-- Every complex entry is absolutely continuous with respect to the
actual positive trace measure. -/
theorem entryMeasure_absolutelyContinuous
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v) (i j : ι) :
    entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  exact entryMeasure_apply_eq_zero_of_traceMeasure_null F ν hfin hν s hs hzero i j

def density (ν : (ι → ℂ) → Measure X) (hfin : ∀ v, IsFiniteMeasure (ν v)) (x : X) :
    Matrix ι ι ℂ := fun i j => (entryMeasure ν hfin i j).rnDeriv (traceMeasure ν) x

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
theorem integrable_density_entry (ν : (ι → ℂ) → Measure X) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : ι) : Integrable (fun x => density ν hfin x i j) (traceMeasure ν) :=
  ComplexMeasure.integrable_rnDeriv _ _

/-- The componentwise actual Radon–Nikodym derivatives recover each
complex entry for every Borel set, with one common reference measure. -/
theorem setIntegral_density_entry
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (s : Set X) (hs : MeasurableSet s) (i j : ι) :
    (∫ x in s, density ν hfin x i j ∂traceMeasure ν) = entryMeasure ν hfin i j s := by
  let c := entryMeasure ν hfin i j
  let μ := traceMeasure ν
  letI : IsFiniteMeasure μ := traceMeasure_isFinite ν hfin
  have hAC := (ComplexMeasure.absolutelyContinuous_ennreal_iff c μ.toENNRealVectorMeasure).mp
    (entryMeasure_absolutelyContinuous F ν hfin hν i j)
  have hInt := (ComplexMeasure.integrable_rnDeriv c μ).integrableOn (s := s)
  change (∫ x in s, c.rnDeriv μ x ∂μ) = c s
  apply Complex.ext
  · change RCLike.re (∫ x in s, c.rnDeriv μ x ∂μ) = _
    rw [← integral_re hInt]
    change (∫ x in s, c.re.rnDeriv μ x ∂μ) = c.re s
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv c.re μ) hs,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hAC.1]
  · change RCLike.im (∫ x in s, c.rnDeriv μ x ∂μ) = _
    rw [← integral_im hInt]
    change (∫ x in s, c.im.rnDeriv μ x ∂μ) = c.im s
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv c.im μ) hs,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hAC.2]

/-- The same constituent densities give an entire positive semidefinite
matrix outside one trace-null set, by simultaneous countable tests. -/
theorem ae_density_posSemidef
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v) :
    ∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef := by
  let μ := traceMeasure ν
  letI : IsFiniteMeasure μ := traceMeasure_isFinite ν hfin
  let q (v : ι → ℂ) (x : X) := quadratic (density ν hfin x) v
  have hterm (v : ι → ℂ) (i j : ι) :
      Integrable (fun x => star (v i) * v j * density ν hfin x i j) μ :=
    (integrable_density_entry ν hfin i j).const_mul _
  have hrow (v : ι → ℂ) (i : ι) :
      Integrable (fun x => ∑ j, star (v i) * v j * density ν hfin x i j) μ :=
    integrable_finset_sum _ fun j _ => hterm v i j
  have hintegrable (v : ι → ℂ) : Integrable (q v) μ :=
    integrable_finset_sum _ fun i _ => hrow v i
  have hInt (v : ι → ℂ) (s : Set X) (hs : MeasurableSet s) :
      (∫ x in s, q v x ∂μ) = ((ν v).real s : ℂ) := by
    rw [← quadratic_entryMeasure_apply F ν hfin hν v s hs]
    change (∫ x in s, ∑ i, ∑ j, star (v i) * v j * density ν hfin x i j ∂μ)
      = ∑ i, ∑ j, star (v i) * v j * entryMeasure ν hfin i j s
    rw [integral_finset_sum _ (fun i _ => (hrow v i).integrableOn)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => (hterm v i j).integrableOn)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, setIntegral_density_entry F ν hfin hν s hs i j]
  have hEach (v : ι → ℂ) : ∀ᵐ x ∂μ, 0 ≤ (q v x).re ∧ (q v x).im = 0 := by
    have hre : 0 ≤ᵐ[μ] fun x => (q v x).re :=
      ae_nonneg_of_forall_setIntegral_nonneg (hintegrable v).re fun s hs _ => by
        change 0 ≤ ∫ x in s, RCLike.re (q v x) ∂μ
        rw [integral_re (hintegrable v).integrableOn, hInt v s hs]
        exact ENNReal.toReal_nonneg
    have him : (fun x => (q v x).im) =ᵐ[μ] 0 :=
      ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => (hintegrable v).im.integrableOn)
        fun s hs _ => by
          change (∫ x in s, RCLike.im (q v x) ∂μ) = 0
          rw [integral_im (hintegrable v).integrableOn, hInt v s hs]
          rfl
    exact hre.and him
  obtain ⟨D, hDcount, hD⟩ := TopologicalSpace.exists_countable_dense (α := ι → ℂ)
  letI : Countable D := hDcount.to_subtype
  have hSimultaneous : ∀ᵐ x ∂μ, ∀ v : D, 0 ≤ (q v x).re ∧ (q v x).im = 0 :=
    ae_all_iff.mpr fun v => hEach v
  filter_upwards [hSimultaneous] with x hx
  apply Burnett.Microlocal.MatrixMeasureAssembly.posSemidef_of_nonneg_real_quadratic
  intro v
  have hq : Continuous (fun v : ι → ℂ => q v x) := by
    unfold q quadratic form
    fun_prop
  exact hD.denseRange_val.induction_on
    (p := fun v => 0 ≤ (q v x).re ∧ (q v x).im = 0) v
    ((isClosed_le continuous_const (Complex.continuous_re.comp hq)).inter
      (isClosed_eq (Complex.continuous_im.comp hq) continuous_const)) hx

end Burnett.Microlocal.MatrixTraceDensity
