import Burnett.Analysis.Microlocal.MatrixMeasure.Polarization
import Burnett.Analysis.Microlocal.MatrixMeasure.Separation
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Complex

/-!
# Assembly of positive Hermitian matrix measures

Polarization builds countably additive complex entries. The same
quadratic measures give positivity and domination by the trace.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.MatrixMeasureAssembly

open MeasureTheory Set Burnett.Microlocal.MatrixPolarization
open scoped BigOperators ComplexOrder Matrix

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]

def weights : Fin 4 → ℂ := ![1 / 4, -1 / 4, -Complex.I / 4, Complex.I / 4]

def basisTests (i j : ι) : Fin 4 → (ι → ℂ) :=
  let u : ι → ℂ := Pi.single i 1
  let v : ι → ℂ := Pi.single j 1
  ![u + (1 : ℂ) • v, u + (-1 : ℂ) • v, u + Complex.I • v, u + (-Complex.I) • v]

theorem entry_eq_weighted_quadratics (A : Matrix ι ι ℂ) (i j : ι) :
    A i j = ∑ k, weights k * quadratic A (basisTests i j k) := by
  have h := form_eq_quadratic_polarization A (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))
  rw [form_single_single] at h
  rw [h, Fin.sum_univ_four]
  simp [weights, basisTests]
  ring

omit [DecidableEq ι] in
private theorem quadratic_conjTranspose (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadratic Aᴴ v = star (quadratic A v) := by
  simp only [quadratic, form, Matrix.conjTranspose_apply, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem posSemidef_of_nonneg_real_quadratic (A : Matrix ι ι ℂ)
    (h : ∀ v, 0 ≤ (quadratic A v).re ∧ (quadratic A v).im = 0) : A.PosSemidef := by
  have heq (v : ι → ℂ) : quadratic Aᴴ v = quadratic A v := by
    rw [quadratic_conjTranspose]
    apply Complex.ext
    · exact Complex.conj_re _
    · rw [Complex.star_def, Complex.conj_im, (h v).2, neg_zero]
  refine ⟨?_, ?_⟩
  · change Aᴴ = A
    ext i j
    rw [entry_eq_weighted_quadratics Aᴴ i j, entry_eq_weighted_quadratics A i j]
    simp only [heq]
  · intro v
    have hdot : star v ⬝ᵥ (A *ᵥ v) = quadratic A v := by
      simp only [quadratic, form, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdot, Complex.nonneg_iff]
    exact ⟨(h v).1, (h v).2.symm⟩

private def asComplex (μ : Measure X) (hμ : IsFiniteMeasure μ) : ComplexMeasure X :=
  letI : IsFiniteMeasure μ := hμ
  μ.toSignedMeasure.toComplexMeasure 0

private theorem asComplex_apply (μ : Measure X) (hμ : IsFiniteMeasure μ)
    (s : Set X) (hs : MeasurableSet s) : asComplex μ hμ s = (μ.real s : ℂ) := by
  letI : IsFiniteMeasure μ := hμ
  rw [asComplex, SignedMeasure.toComplexMeasure_apply, Measure.toSignedMeasure_apply_measurable hs]
  rfl

/-- Polarized entry as an actual complex vector measure. Countable
additivity follows from the vector measure type and its module operations. -/
def entryMeasure (ν : (ι → ℂ) → Measure X) (hν : ∀ v, IsFiniteMeasure (ν v)) (i j : ι) :
    ComplexMeasure X :=
  ∑ k, weights k • asComplex (ν (basisTests i j k)) (hν (basisTests i j k))

omit [Fintype ι] in
theorem entryMeasure_apply (ν : (ι → ℂ) → Measure X) (hν : ∀ v, IsFiniteMeasure (ν v))
    (i j : ι) (s : Set X) (hs : MeasurableSet s) :
    entryMeasure ν hν i j s = ∑ k, weights k * ((ν (basisTests i j k)).real s : ℂ) := by
  let eval : ComplexMeasure X →+ ℂ :=
    { toFun := fun m => m s
      map_zero' := rfl
      map_add' := fun _ _ => VectorMeasure.add_apply _ _ s }
  change eval (∑ k, weights k • asComplex (ν (basisTests i j k)) (hν (basisTests i j k))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (weights k • asComplex (ν (basisTests i j k)) (hν (basisTests i j k))) s = _
  rw [VectorMeasure.smul_apply, asComplex_apply _ _ _ hs, smul_eq_mul]

variable [TopologicalSpace X] [CompactSpace X]

def testMatrix (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (f : C(X, ℂ)) : Matrix ι ι ℂ :=
  fun i j => F i j f

omit [CompactSpace X] in
/-- Every matrix entry is represented by the four actual positive measures
from its basis-pair quadratic tests. -/
theorem entryFunctional_eq_integral_polarization
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (i j : ι) (f : C(X, ℂ)) :
    F i j f = ∑ k, weights k * (∫ x, f x ∂ν (basisTests i j k)) := by
  simp_rw [hν]
  exact entry_eq_weighted_quadratics (testMatrix F f) i j

variable [BorelSpace X] [HasOuterApproxClosed X]

/-- On each Borel set the genuine polarized matrix measures recover the
same positive measure for every constant-vector quadratic contraction. -/
theorem quadratic_entryMeasure_apply
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (v : ι → ℂ) (s : Set X) (hs : MeasurableSet s) :
    quadratic (fun i j => entryMeasure ν hfin i j s) v = ((ν v).real s : ℂ) := by
  classical
  let bundle : Unit ⊕ (ι × ι × Fin 4) → Measure X :=
    Sum.elim (fun _ => ν v) fun t => ν (basisTests t.1 t.2.1 t.2.2)
  let c : Unit ⊕ (ι × ι × Fin 4) → ℂ :=
    Sum.elim (fun _ => -1) fun t => star (v t.1) * v t.2.1 * weights t.2.2
  have hBundle : ∀ k, IsFiniteMeasure (bundle k) := by
    intro k
    cases k
    · exact hfin v
    · exact hfin _
  have reduce (r : Measure X → ℂ) : ∑ k, c k * r (bundle k) =
      -r (ν v) + ∑ i, ∑ j, star (v i) * v j *
        ∑ k, weights k * r (ν (basisTests i j k)) := by
    rw [Fintype.sum_sum_type]
    simp only [c, bundle, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, neg_one_mul]
    simp_rw [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  have hzero (f : C(X, ℝ)) : ∑ k, c k * ((∫ x, f x ∂bundle k : ℝ) : ℂ) = 0 := by
    let cf : C(X, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    have hint (μ : Measure X) : ((∫ x, f x ∂μ : ℝ) : ℂ) = ∫ x, cf x ∂μ :=
      (integral_complex_ofReal (μ := μ) (f := (f : X → ℝ))).symm
    rw [reduce (fun μ => ((∫ x, f x ∂μ : ℝ) : ℂ))]
    simp_rw [hint]
    rw [hν v cf]
    simp_rw [← entryFunctional_eq_integral_polarization F ν hν]
    exact neg_add_cancel (quadratic (testMatrix F cf) v)
  have h := Burnett.Microlocal.MeasureSeparation.sum_complex_measure_real_eq_zero_of_integral_eq_zero
    bundle hBundle c hzero s
  rw [reduce (fun μ => (μ.real s : ℂ))] at h
  simp_rw [← entryMeasure_apply ν hfin _ _ s hs] at h
  change -(↑((ν v).real s) : ℂ) + quadratic (fun i j => entryMeasure ν hfin i j s) v = 0 at h
  rw [add_comm, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp h

/-- The resulting complex matrix of measures is positive semidefinite on
every Borel set, for the same entry measures and all constant vectors. -/
theorem entryMeasure_posSemidef
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (s : Set X) (hs : MeasurableSet s) :
    Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ) := by
  apply posSemidef_of_nonneg_real_quadratic
  intro v
  rw [quadratic_entryMeasure_apply F ν hfin hν v s hs]
  exact ⟨ENNReal.toReal_nonneg, Complex.ofReal_im _⟩

/-- The positive trace measure is the sum of the diagonal quadratic
measures, each evaluated at the corresponding basis vector. -/
def traceMeasure (ν : (ι → ℂ) → Measure X) : Measure X :=
  ∑ i, ν (Pi.single i 1)

/-- Every actual complex entry vanishes on trace-null Borel sets. -/
theorem entryMeasure_apply_eq_zero_of_traceMeasure_null
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (s : Set X) (hs : MeasurableSet s) (htrace : traceMeasure ν s = 0) :
    ∀ i j, entryMeasure ν hfin i j s = 0 := by
  let A : Matrix ι ι ℂ := fun i j => entryMeasure ν hfin i j s
  have hDiag (i : ι) : A i i = 0 := by
    have hzero : ν (Pi.single i 1) s = 0 := by
      apply nonpos_iff_eq_zero.mp
      calc
        _ ≤ ∑ j, ν (Pi.single j 1) s :=
          Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)
        _ = 0 := by simpa only [traceMeasure, Measure.finset_sum_apply] using htrace
    have hcomp := quadratic_entryMeasure_apply F ν hfin hν (Pi.single i 1) s hs
    change form A (Pi.single i 1) (Pi.single i 1) = _ at hcomp
    rw [form_single_single, measureReal_def, hzero, ENNReal.toReal_zero, Complex.ofReal_zero] at hcomp
    exact hcomp
  have htr : Matrix.trace A = 0 := Finset.sum_eq_zero (fun i _ => hDiag i)
  have hA : A = 0 := (entryMeasure_posSemidef F ν hfin hν s hs).trace_eq_zero_iff.mp htr
  intro i j
  change A i j = 0
  rw [hA, Matrix.zero_apply]

end Burnett.Microlocal.MatrixMeasureAssembly
