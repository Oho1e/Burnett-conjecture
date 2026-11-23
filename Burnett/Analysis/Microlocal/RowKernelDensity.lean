import Burnett.Analysis.Microlocal.SeparableCrossPairings
import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Burnett.Analysis.Microlocal.PositiveKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RowKernelDensity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.MatrixPolarization
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

/-- Aggregate all finite row terms which act on the same input component. -/
def groupRow {I J : Type} [DecidableEq I] [Fintype J]
    (component : J → I) (t : J → ℂ) (i : I) : ℂ :=
  ∑ s, if component s = i then t s else 0

private theorem sum_groupRow_mul {I J : Type} [DecidableEq I] [Fintype I] [Fintype J]
    (component : J → I) (t : J → ℂ) (b : I → ℂ) :
    (∑ i, groupRow component t i * b i) = ∑ s, t s * b (component s) := by
  simp only [groupRow, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem quadratic_groupRow {I J : Type} [DecidableEq I] [Fintype I] [Fintype J]
    (D : Matrix I I ℂ) (component : J → I) (t : J → ℂ) :
    quadratic D (groupRow component t) =
      ∑ s, ∑ t', conj (t s) * t t' * D (component s) (component t') := by
  let R := groupRow component t
  have hc (i : I) : star (R i) = groupRow component (fun s => conj (t s)) i := by
    change conj (∑ s, if component s = i then t s else 0) = _
    simp only [groupRow, map_sum, apply_ite, map_zero]
  calc
    quadratic D R = ∑ i, groupRow component (fun s => conj (t s)) i * (∑ j, R j * D i j) := by
      simp only [quadratic, form, hc, Finset.mul_sum, mul_assoc]
    _ = ∑ s, conj (t s) * (∑ j, R j * D (component s) j) :=
      sum_groupRow_mul component _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [sum_groupRow_mul component t]
      simp only [Finset.mul_sum, mul_assoc]

private theorem quadratic_eq_dotProduct {I : Type} [Fintype I]
    (D : Matrix I I ℂ) (v : I → ℂ) :
    quadratic D v = star v ⬝ᵥ (D *ᵥ v) := by
  simp only [quadratic, form, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- With the operator-second density orientation the corresponding physical
row annihilates the transpose of the density almost everywhere. -/
theorem ae_quadratic_zero_and_row_kernel_of_integral_zero {I X : Type} [Fintype I]
    [MeasurableSpace X] (τ : Measure X) (D : X → Matrix I I ℂ) (A : X → I → ℂ)
    (hPSD : ∀ᵐ x ∂τ, (D x).PosSemidef)
    (hInt : Integrable (fun x => quadratic (D x) (A x)) τ)
    (hzero : (∫ x, quadratic (D x) (A x) ∂τ) = 0) :
    ∀ᵐ x ∂τ, quadratic (D x) (A x) = 0 ∧ A x ᵥ* (D x)ᵀ = 0 := by
  have hsign : ∀ᵐ x ∂τ, 0 ≤ (quadratic (D x) (A x)).re ∧ (quadratic (D x) (A x)).im = 0 := by
    filter_upwards [hPSD] with x hx
    have hs : 0 ≤ quadratic (D x) (A x) := by
      rw [quadratic_eq_dotProduct]
      exact hx.2 _
    exact ⟨(Complex.nonneg_iff.mp hs).1, (Complex.nonneg_iff.mp hs).2.symm⟩
  have hreInt : (∫ x, (quadratic (D x) (A x)).re ∂τ) = 0 := by
    change (∫ x, RCLike.re (quadratic (D x) (A x)) ∂τ) = 0
    rw [integral_re hInt, hzero]
    rfl
  have hzre : (fun x => (quadratic (D x) (A x)).re) =ᵐ[τ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hsign.mono fun _ hx => hx.1) hInt.re).mp hreInt
  filter_upwards [hPSD, hsign, hzre] with x hD hq hre
  have heq : quadratic (D x) (A x) = 0 := Complex.ext hre hq.2
  refine ⟨heq, ?_⟩
  rw [Matrix.vecMul_transpose]
  apply (hD.dotProduct_mulVec_zero_iff (A x)).mp
  rw [← quadratic_eq_dotProduct]
  exact heq

end Burnett.Microlocal.RowKernelDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RowKernelDensity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixPolarization
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate ComplexOrder Matrix

/-- The actual left-to-right finite row action, with each term's original input selector. -/
def separableRowAction {I J : Type} [Fintype J] (component : J → I)
    (a m : J → BoundedSymbol Space) (u : I → ComplexL2 Space) : ComplexL2 Space :=
  ∑ s, separableOperator (a s) (m s) (u (component s))

/-- The grouped physical row on the actual compact coordinate-cosphere product. -/
def separableRowCoefficients {I J : Type} [DecidableEq I] [Fintype J] (K : BallData)
    (component : J → I) (a m : J → BoundedSymbol Space) (x : Chart K) : I → ℂ :=
  groupRow component (fun s => a s x.1 * m s x.2)

private def termRestriction (K : BallData) (a m : BoundedSymbol Space)
    (ha : Continuous (a : Space → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space)) : TestSpace K :=
  finiteSmoothRestriction K (fun _ : Unit => a) (fun _ => m) (fun _ => ha) (fun _ => hm)

private theorem termRestriction_apply (K : BallData) (a m : BoundedSymbol Space)
    (ha : Continuous (a : Space → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space)) (x : Chart K) :
    termRestriction K a m ha hm x = a x.1 * m x.2 := by
  obtain ⟨y, ξ⟩ := x
  simp only [termRestriction, finiteSmoothRestriction_apply, Fintype.sum_unique]

/-- An actual strongly null finite row forces zero quadratic integral and
the physical transpose-oriented row-kernel equation for the same fixed subsequence. -/
theorem row_integral_zero_and_ae_kernel_of_squareLimits {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J]
    (K : BallData) (component : J → I) (a m : J → BoundedSymbol Space)
    (ha : ∀ s, Continuous (a s : Space → ℂ))
    (hm : ∀ s, ContDiffOn ℝ ∞ (m s : Space → ℂ) ({0}ᶜ : Set Space))
    (u : ℕ → I → ComplexL2 Space) (B : ℝ) (hB : ∀ n i, ‖u n i‖ ≤ B)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (τ : Measure (Chart K)) (D : Chart K → Matrix I I ℂ)
    (hIntD : ∀ i j, Integrable (fun x => D x i j) τ)
    (hPSD : ∀ᵐ x ∂τ, (D x).PosSemidef)
    (hcomm : ∀ s t, Tendsto (fun n =>
      cutoffCommutator (m t) (productSymbol (conjugateSymbol (a s)) (a t)) (u n (component t)))
      atTop (𝓝 0))
    (hlim : ∀ s t, Tendsto (fun n =>
      inner ℂ (u (σ n) (component s))
        (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t))))
      atTop (𝓝 (∫ x, conj (a s x.1 * m s x.2) * (a t x.1 * m t x.2) *
        D x (component s) (component t) ∂τ)))
    (hStrong : Tendsto (fun n => separableRowAction component a m (u n)) atTop (𝓝 0)) :
    let R := separableRowCoefficients K component a m
    (∫ x, quadratic (D x) (R x) ∂τ) = 0 ∧
      (∀ᵐ x ∂τ, quadratic (D x) (R x) = 0 ∧ R x ᵥ* (D x)ᵀ = 0) := by
  intro R
  let T (s : J) := separableOperator (a s) (m s)
  let Q (s t : J) (n : ℕ) :=
    inner ℂ (T s (u (σ n) (component s))) (T t (u (σ n) (component t)))
  let P (s t : J) (n : ℕ) :=
    inner ℂ (u (σ n) (component s))
      (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t)))
  let g (s t : J) (x : Chart K) :=
    conj (a s x.1 * m s x.2) * (a t x.1 * m t x.2) * D x (component s) (component t)
  have he (s t : J) : Tendsto (fun n => Q s t n - P s t n) atTop (𝓝 0) := by
    have h := separableOperator_cross_difference_tendsto_zero (a t) (a s) (m t) (m s)
      (fun n => u n (component t)) (fun n => u n (component s)) B
      (fun n => hB n (component t)) (hcomm t s)
    have hc := (Complex.continuous_conj.tendsto (0 : ℂ)).comp (h.comp hσ.tendsto_atTop)
    rw [map_zero] at hc
    apply hc.congr
    intro n
    change conj (Q t s n - inner ℂ
      (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t)))
      (u (σ n) (component s))) = _
    rw [map_sub]
    congr 1
    · exact inner_conj_symm _ _
    · exact inner_conj_symm _ _
  have hQ (s t : J) : Tendsto (Q s t) atTop (𝓝 (∫ x, g s t x ∂τ)) := by
    have h := (he s t).add (hlim s t)
    change Tendsto (fun n => (Q s t n - P s t n) + P s t n)
      atTop (𝓝 (0 + ∫ x, g s t x ∂τ)) at h
    simpa only [sub_add_cancel, zero_add] using h
  have hRow : Tendsto (fun n =>
      inner ℂ (separableRowAction component a m (u (σ n)))
        (separableRowAction component a m (u (σ n))))
      atTop (𝓝 (∑ s, ∑ t, ∫ x, g s t x ∂τ)) := by
    apply (tendsto_finset_sum Finset.univ (fun s _ =>
      tendsto_finset_sum Finset.univ (fun t _ => hQ s t))).congr
    intro n
    symm
    change inner ℂ (∑ s, T s (u (σ n) (component s)))
      (∑ t, T t (u (σ n) (component t))) = ∑ s, ∑ t, Q s t n
    rw [sum_inner]
    simp only [inner_sum, Q]
  have hs := hStrong.comp hσ.tendsto_atTop
  have hZero : Tendsto (fun n =>
      inner ℂ (separableRowAction component a m (u (σ n)))
        (separableRowAction component a m (u (σ n)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, inner_zero_right] using hs.inner (𝕜 := ℂ) hs
  have hsumZero : (∑ s, ∑ t, ∫ x, g s t x ∂τ) = 0 :=
    tendsto_nhds_unique hRow hZero
  have hInt (s t : J) : Integrable (g s t) τ := by
    let H := star (termRestriction K (a s) (m s) (ha s) (hm s)) *
      termRestriction K (a t) (m t) (ha t) (hm t)
    have h := (hIntD (component s) (component t)).bdd_mul H.continuous.aestronglyMeasurable
      ⟨‖H‖, H.norm_coe_le_norm⟩
    simpa only [g, H, ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.star_def,
      termRestriction_apply] using h
  have hrowInt (s : J) : Integrable (fun x => ∑ t, g s t x) τ :=
    integrable_finset_sum _ (fun t _ => hInt s t)
  have hq (x : Chart K) : quadratic (D x) (R x) = ∑ s, ∑ t, g s t x :=
    quadratic_groupRow (D x) component (fun s => a s x.1 * m s x.2)
  have hQInt : Integrable (fun x => quadratic (D x) (R x)) τ := by
    simp_rw [hq]
    exact integrable_finset_sum _ (fun s _ => hrowInt s)
  have hIntegral : (∫ x, quadratic (D x) (R x) ∂τ) = 0 := by
    simp_rw [hq]
    rw [integral_finset_sum _ (fun s _ => hrowInt s)]
    have hSwap (s : J) :
        (∫ x, ∑ t, g s t x ∂τ) = ∑ t, ∫ x, g s t x ∂τ :=
      integral_finset_sum _ (fun t _ => hInt s t)
    simp_rw [hSwap]
    exact hsumZero
  exact ⟨hIntegral, ae_quadratic_zero_and_row_kernel_of_integral_zero τ D R hPSD hQInt hIntegral⟩

end Burnett.Microlocal.RowKernelDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RowKernelDensity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixPolarization Burnett.Microlocal.MatrixMeasureAssembly
open Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate ComplexOrder Matrix

/-- A strongly null finite separated row annihilates the already constructed trace density.
All pair products are actual finite separated tests on the same subsequence. -/
theorem row_density_kernel_of_localized_weak_zero {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J]
    (K : BallData) (component : J → I) (a m : J → BoundedSymbol Space)
    (hsa : ∀ s, ContDiff ℝ ∞ (a s : Space → ℂ))
    (hca : ∀ s, HasCompactSupport (a s : Space → ℂ))
    (hsm : ∀ s, ContDiffOn ℝ ∞ (m s : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ s, DegreeZero (m s : Space → ℂ))
    (f : ℕ → I → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : I) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (I → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hPSD : ∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef)
    (hLimits : ∀ (L : Type) [Fintype L] (b p : L → BoundedSymbol Space)
        (hb : ∀ j, Continuous (b j : Space → ℂ))
        (hp : ∀ j, ContDiffOn ℝ ∞ (p j : Space → ℂ) ({0}ᶜ : Set Space))
        (_ : ∀ j, DegreeZero (p j : Space → ℂ)) (i j : I),
      let q := finiteSmoothRestriction K b p hb hp
      Tendsto (fun n =>
        let u₁ := (sourceSchwartz (hs (σ n) i) χ₀ (hχ₀ (σ n) i)).toLp 2 volume
        let u₂ := (sourceSchwartz (hs (σ n) j) χ₀ (hχ₀ (σ n) j)).toLp 2 volume
        inner ℂ u₁ (finiteSeparableOperator b p u₂))
        atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν)))
    (hStrong : Tendsto (fun n => separableRowAction component a m
      (fun c => (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume)) atTop (𝓝 0)) :
    let R := separableRowCoefficients K component a m
    (∫ x, quadratic (density ν hfin x) (R x) ∂traceMeasure ν) = 0 ∧
      (∀ᵐ x ∂traceMeasure ν, quadratic (density ν hfin x) (R x) = 0 ∧
        R x ᵥ* (density ν hfin x)ᵀ = 0) := by
  let u (n : ℕ) (c : I) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
  have hu (n : ℕ) (c : I) : ‖u n c‖ ≤ B := by
    have heq : ‖u n c‖ = ‖(hf n c).toLp (f n c)‖ := by
      simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f n c x))
    exact heq.trans_le (hB n c)
  have hcomm (s t : J) :
      Tendsto (fun n => cutoffCommutator (m t)
        (productSymbol (conjugateSymbol (a s)) (a t)) (u n (component t))) atTop (𝓝 0) := by
    let b := productSymbol (conjugateSymbol (a s)) (a t)
    have hsb : ContDiff ℝ ∞ (b : Space → ℂ) :=
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (hsa s)).mul (hsa t)
    have hcb : HasCompactSupport (b : Space → ℂ) :=
      ((hca s).comp_left (by simp : (starRingEnd ℂ) 0 = 0)).mul_right
    exact cutoffCommutator_tendsto_zero_of_localized_weak_zero (m t) b (hsm t) (hd t) hsb hcb
      (fun n => f n (component t)) (fun n => hs n (component t)) (fun n => hf n (component t))
      χ₀ (fun n => hχ₀ n (component t)) B (fun n => hB n (component t)) (ht (component t))
  apply row_integral_zero_and_ae_kernel_of_squareLimits K component a m
    (fun s => (hsa s).continuous) hsm u B hu σ hσ (traceMeasure ν) (density ν hfin)
    (integrable_density_entry ν hfin) hPSD hcomm _ hStrong
  intro s t
  let b (_ : Unit) := productSymbol (a t) (conjugateSymbol (a s))
  let p (_ : Unit) := productSymbol (conjugateSymbol (m s)) (m t)
  have hb (j : Unit) : Continuous (b j : Space → ℂ) :=
    (hsa t).continuous.mul (Complex.continuous_conj.comp (hsa s).continuous)
  have hp (j : Unit) : ContDiffOn ℝ ∞ (p j : Space → ℂ) ({0}ᶜ : Set Space) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (hsm s)).mul (hsm t)
  have hd' (j : Unit) : DegreeZero (p j : Space → ℂ) := by
    intro r hr x
    simp only [p, productSymbol_apply, conjugateSymbol_apply, hd s r hr x, hd t r hr x]
  have hOp : finiteSeparableOperator b p = squareSymbolTerm (a t) (a s) (m t) (m s) := by
    simp only [finiteSeparableOperator, Fintype.sum_unique, b, p, squareSymbolTerm]
  have hq (x : Chart K) : finiteSmoothRestriction K b p hb hp x =
      conj (a s x.1 * m s x.2) * (a t x.1 * m t x.2) := by
    obtain ⟨y, ξ⟩ := x
    simp only [finiteSmoothRestriction_apply, Fintype.sum_unique, b, p, productSymbol_apply,
      conjugateSymbol_apply, map_mul]
    ring
  have h := hLimits Unit b p hb hp hd' (component s) (component t)
  simpa only [hOp, hq] using h

end Burnett.Microlocal.RowKernelDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RowKernelDensity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixPolarization Burnett.Microlocal.MatrixMeasureAssembly
open Burnett.Microlocal.MatrixTraceDensity Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.BesselLocalization
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexOrder Matrix

/-- On the round unit cosphere the exact Bessel principal row has a common
Fourier factor of the imaginary unit times the real directional coefficient. -/
theorem rowPrincipalCoefficients_eq_round {I J : Type} [DecidableEq I] [Fintype J]
    (K : BallData) (component : J → I) (a : J → D) (v : J → Space)
    (x : Chart K) (i : I) :
    separableRowCoefficients K component
      (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (v s)) x i =
        Complex.I * ∑ s, if component s = i then
          (((a s : Space → ℝ) x.1 * inner ℝ (x.2 : Space) (v s) : ℝ) : ℂ) else 0 := by
  have hnorm : ‖(x.2 : Space)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2.property
  unfold separableRowCoefficients groupRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : component s = i
  · simp only [h, if_true, physicalCoefficient, angularDirectionSymbol, angularDirection,
      hnorm, div_one, Complex.ofReal_mul]
    ring
  · simp only [h, if_false, mul_zero]

/-- The coefficients and normalized directions of the actual Bessel principal
row satisfy the transpose kernel equation for the same compact trace density. -/
theorem rowPrincipal_density_kernel_of_strong_zero {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J]
    (K : BallData) (component : J → I) (a : J → D) (v : J → Space)
    (f : ℕ → I → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : D) (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : I) (φ : D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (I → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hPSD : ∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef)
    (hLimits : ∀ (L : Type) [Fintype L] (b p : L → BoundedSymbol Space)
        (hb : ∀ j, Continuous (b j : Space → ℂ))
        (hp : ∀ j, ContDiffOn ℝ ∞ (p j : Space → ℂ) ({0}ᶜ : Set Space))
        (_ : ∀ j, DegreeZero (p j : Space → ℂ)) (i j : I),
      let q := finiteSmoothRestriction K b p hb hp
      Tendsto (fun n =>
        let u₁ := (sourceSchwartz (hs (σ n) i) χ₀ (hχ₀ (σ n) i)).toLp 2 volume
        let u₂ := (sourceSchwartz (hs (σ n) j) χ₀ (hχ₀ (σ n) j)).toLp 2 volume
        inner ℂ u₁ (finiteSeparableOperator b p u₂))
        atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν)))
    (hStrong : Tendsto (fun n => rowPrincipal a v component
      (fun c => sourceSchwartz (hs n c) χ₀ (hχ₀ n c))) atTop (𝓝 0)) :
    let R := separableRowCoefficients K component
      (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (v s))
    (∫ x, quadratic (density ν hfin x) (R x) ∂traceMeasure ν) = 0 ∧
      (∀ᵐ x ∂traceMeasure ν, quadratic (density ν hfin x) (R x) = 0 ∧
        R x ᵥ* (density ν hfin x)ᵀ = 0) := by
  refine row_density_kernel_of_localized_weak_zero K component
    (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (v s))
    (fun s => Complex.ofRealCLM.contDiff.comp (test_smooth (a s)))
    (fun s => (test_compactSupport (a s)).comp_left Complex.ofReal_zero)
    (fun s => angularDirection_contDiffOn (v s)) (fun s => angularDirection_degreeZero (v s))
    f hs hf χ₀ hχ₀ B hB ht σ hσ ν hfin hPSD hLimits ?_
  exact hStrong

end Burnett.Microlocal.RowKernelDensity
