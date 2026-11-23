import Burnett.Analysis.Microlocal.CompactJetMatrixMeasure
import Burnett.Analysis.Microlocal.MatrixMeasure.TraceDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CompactChartDensity

open MeasureTheory Set Burnett.Microlocal.MatrixPolarization
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open scoped BigOperators ComplexOrder Matrix

section CompactMeasure

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X]

private theorem compressionMeasure_absolutelyContinuous
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v)
    (v : ι → ℂ) : ν v ≪ traceMeasure ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hτ
  have hzero := entryMeasure_apply_eq_zero_of_traceMeasure_null F ν hfin hν s hs hτ
  have h := quadratic_entryMeasure_apply F ν hfin hν v s hs
  have hq : quadratic (fun i j => entryMeasure ν hfin i j s) v = 0 := by
    simp only [quadratic, form, hzero, mul_zero, Finset.sum_const_zero]
  have he : ((ν v).real s : ℂ) = 0 := h.symm.trans hq
  have hr : (ν v).real s = 0 := Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using he)
  letI := hfin v
  exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right (measure_lt_top (ν v) s).ne

private def compressionDensity (ν : (ι → ℂ) → Measure X) (v : ι → ℂ) (x : X) : ℂ :=
  ((ν v).rnDeriv (traceMeasure ν) x).toReal

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
private theorem integrable_compressionDensity
    (ν : (ι → ℂ) → Measure X) (hfin : ∀ v, IsFiniteMeasure (ν v)) (v : ι → ℂ) :
    Integrable (compressionDensity ν v) (traceMeasure ν) := by
  letI := hfin v
  have hr : Integrable (fun x => ((ν v).rnDeriv (traceMeasure ν) x).toReal) (traceMeasure ν) :=
    integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv (ν v) (traceMeasure ν)).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top (ν v) (traceMeasure ν)).ne
  exact hr.ofReal

private theorem setIntegral_compressionDensity
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v)
    (v : ι → ℂ) (s : Set X) :
    (∫ x in s, compressionDensity ν v x ∂traceMeasure ν) = ((ν v).real s : ℂ) := by
  letI := hfin v
  letI := traceMeasure_isFinite ν hfin
  unfold compressionDensity
  rw [integral_complex_ofReal,
    Measure.setIntegral_toReal_rnDeriv (compressionMeasure_absolutelyContinuous F ν hfin hν v) s]

private theorem ae_entry_density_eq_polarization
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v) (i j : ι) :
    (fun x => density ν hfin x i j) =ᵐ[traceMeasure ν]
      (fun x => ∑ k, weights k * compressionDensity ν (basisTests i j k) x) := by
  letI := traceMeasure_isFinite ν hfin
  have hInt (k : Fin 4) :
      Integrable (fun x => weights k * compressionDensity ν (basisTests i j k) x) (traceMeasure ν) :=
    (integrable_compressionDensity ν hfin _).const_mul _
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => (integrable_density_entry ν hfin i j).integrableOn)
    (fun _ _ _ => (integrable_finset_sum _ (fun k _ => hInt k)).integrableOn)
  intro s hs _
  rw [setIntegral_density_entry F ν hfin hν s hs i j, entryMeasure_apply ν hfin i j s hs,
    integral_finset_sum _ (fun k _ => (hInt k).integrableOn)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, setIntegral_compressionDensity F ν hfin hν]

private theorem integral_mul_compressionDensity
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v)
    (v : ι → ℂ) (q : C(X, ℂ)) :
    (∫ x, q x * compressionDensity ν v x ∂traceMeasure ν) = ∫ x, q x ∂ν v := by
  let μ := traceMeasure ν
  letI := hfin v
  letI := traceMeasure_isFinite ν hfin
  have hμ : μ.withDensity ((ν v).rnDeriv μ) = ν v :=
    Measure.withDensity_rnDeriv_eq _ _ (compressionMeasure_absolutelyContinuous F ν hfin hν v)
  calc
    _ = ∫ x, ((ν v).rnDeriv μ x).toReal • q x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [compressionDensity, Complex.real_smul, μ, mul_comm]
    _ = ∫ x, q x ∂μ.withDensity ((ν v).rnDeriv μ) :=
      (integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv (ν v) μ)
        (Measure.rnDeriv_lt_top (ν v) μ) (q : X → ℂ)).symm
    _ = _ := by rw [hμ]

/-- Every continuous complex test integrates against the entry density
for the same trace measure used in the Borel-set identities. -/
theorem entryFunctional_eq_integral_density
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v)
    (i j : ι) (q : C(X, ℂ)) :
    F i j q = ∫ x, q x * density ν hfin x i j ∂traceMeasure ν := by
  let p (k : Fin 4) := compressionDensity ν (basisTests i j k)
  have hInt (k : Fin 4) :
      Integrable (fun x => weights k * (q x * p k x)) (traceMeasure ν) :=
    ((integrable_compressionDensity ν hfin _).bdd_mul q.continuous.aestronglyMeasurable
      ⟨‖q‖, q.norm_coe_le_norm⟩).const_mul _
  calc
    _ = ∑ k, weights k * (∫ x, q x ∂ν (basisTests i j k)) :=
      entryFunctional_eq_integral_polarization F ν hν i j q
    _ = ∑ k, weights k * (∫ x, q x * p k x ∂traceMeasure ν) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← integral_mul_compressionDensity F ν hfin hν (basisTests i j k) q]
    _ = ∫ x, ∑ k, weights k * (q x * p k x) ∂traceMeasure ν := by
      rw [integral_finset_sum _ (fun k _ => hInt k)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_entry_density_eq_polarization F ν hfin hν i j] with x hx
      change density ν hfin x i j = ∑ k, weights k * p k x at hx
      rw [hx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The actual matrix density has trace one outside a trace-null set. -/
theorem ae_density_trace_eq_one
    (F : ι → ι → (C(X, ℂ) →L[ℂ] ℂ)) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v) :
    ∀ᵐ x ∂traceMeasure ν, Matrix.trace (density ν hfin x) = 1 := by
  let μ := traceMeasure ν
  letI : IsFiniteMeasure μ := traceMeasure_isFinite ν hfin
  have hInt : Integrable (fun x => Matrix.trace (density ν hfin x)) μ :=
    integrable_finset_sum _ fun i _ => integrable_density_entry ν hfin i i
  have hOne : Integrable (fun _ : X => (1 : ℂ)) μ := integrable_const 1
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hInt.integrableOn) (fun _ _ _ => hOne.integrableOn)
  intro s hs _
  change (∫ x in s, ∑ i, density ν hfin x i i ∂traceMeasure ν) = ∫ _ in s, (1 : ℂ) ∂traceMeasure ν
  rw [integral_finset_sum _ (fun i _ => (integrable_density_entry ν hfin i i).integrableOn)]
  simp_rw [setIntegral_density_entry F ν hfin hν s hs]
  have hdiag (i : ι) : entryMeasure ν hfin i i s = ((ν (Pi.single i 1)).real s : ℂ) := by
    have h := quadratic_entryMeasure_apply F ν hfin hν (Pi.single i 1) s hs
    change form (fun j k => entryMeasure ν hfin j k s) (Pi.single i 1) (Pi.single i 1) = _ at h
    rwa [form_single_single] at h
  simp_rw [hdiag]
  rw [← Complex.ofReal_sum]
  have htrace : (traceMeasure ν).real s = ∑ i, (ν (Pi.single i 1)).real s := by
    simp only [traceMeasure, measureReal_def, Measure.finset_sum_apply]
    apply ENNReal.toReal_sum
    intro i _
    letI := hfin (Pi.single i 1)
    exact (measure_lt_top (ν (Pi.single i 1)) s).ne
  rw [← htrace, integral_const]
  simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, Complex.real_smul]

end CompactMeasure

end Burnett.Microlocal.CompactChartDensity

namespace Burnett.Microlocal.CompactChartDensity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart exists_compactChartMatrixMeasure_of_localized_weak_zero)
open Burnett.Microlocal.MatrixPolarization Burnett.Microlocal.MatrixMeasureAssembly
open Burnett.Microlocal.MatrixTraceDensity
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexOrder Matrix

/-- The same actual compact-chart witnesses have one common trace density, with set
integrals, all continuous weighted tests, and every finite-list pairing on the same subsequence. -/
theorem exists_compactChartMatrixDensity_of_localized_weak_zero {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (K : BallData) (f : ℕ → ι → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : ι) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u (n : ℕ) (c : ι) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ F : ι → ι → (TestSpace K →L[ℂ] ℂ),
      ∃ ν : (ι → ℂ) → Measure (Chart K),
      ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        (∀ v, (ν v).Regular) ∧
        (∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v) ∧
        (∀ i j q,
          F i j q = ∑ k, weights k * (∫ x, q x ∂ν (basisTests i j k)) ∧
          F i j q = ∫ x, q x * density ν hfin x i j ∂traceMeasure ν) ∧
        (∀ ps i j, let q := separableRestriction K ps
          Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
            atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν))) ∧
        (∀ v (s : Set (Chart K)), MeasurableSet s →
          quadratic (fun i j => entryMeasure ν hfin i j s) v = ((ν v).real s : ℂ)) ∧
        (∀ s : Set (Chart K), MeasurableSet s →
          Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ)) ∧
        IsFiniteMeasure (traceMeasure ν) ∧
        (∀ i j, entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure) ∧
        (∀ s : Set (Chart K), MeasurableSet s → ∀ i j,
          (∫ x in s, density ν hfin x i j ∂traceMeasure ν) = entryMeasure ν hfin i j s) ∧
        (∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef ∧ Matrix.trace (density ν hfin x) = 1) := by
  intro u
  obtain ⟨σ, hσ, F, ν, hfin, hReg, hRep, hPolar, hPair, hCompress, hPSD, hTraceFin, hAC⟩ :=
    exists_compactChartMatrixMeasure_of_localized_weak_zero K f hs hf χ₀ hχ₀ hKf B hB ht
  have hWeighted := entryFunctional_eq_integral_density F ν hfin hRep
  refine ⟨σ, hσ, F, ν, hfin, hReg, hRep, fun i j q => ⟨hPolar i j q, hWeighted i j q⟩,
    ?_, hCompress, hPSD, hTraceFin, hAC, setIntegral_density_entry F ν hfin hRep,
    (ae_density_posSemidef F ν hfin hRep).and (ae_density_trace_eq_one F ν hfin hRep)⟩
  intro ps i j
  dsimp only
  rw [← hWeighted i j (separableRestriction K ps), hPolar]
  exact hPair ps i j

end Burnett.Microlocal.CompactChartDensity
