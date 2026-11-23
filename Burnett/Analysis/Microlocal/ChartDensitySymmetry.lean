import Burnett.Analysis.Microlocal.RoundChartCovariance
import Burnett.Analysis.Microlocal.RowKernelDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.FixedChartGeometricDensity

open MeasureTheory Filter Set Matrix Burnett.Fourier
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixPolarization Burnett.Microlocal.RowKernelDensity
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff ComplexConjugate ComplexOrder Matrix Topology

/-- The constant-one symbol is an admissible separated test both in the base
and in the frequency, including at the infrared origin. -/
def unitChartSymbol : BoundedSymbol Space where
  toFun := fun _ => 1
  measurable := aestronglyMeasurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun _ => by simp

private theorem unitChartSymbol_continuous : Continuous (unitChartSymbol : Space → ℂ) :=
  continuous_const

private theorem unitChartSymbol_smooth :
    ContDiffOn ℝ ∞ (unitChartSymbol : Space → ℂ) ({0}ᶜ : Set Space) :=
  contDiffOn_const

private theorem unitChartSymbol_degreeZero : DegreeZero (unitChartSymbol : Space → ℂ) :=
  fun _ _ _ => rfl

private abbrev unitChartTest : Unit → BoundedSymbol Space := fun _ => unitChartSymbol

private theorem unitChartRestriction_apply (K : BallData) (x : Chart K) :
    finiteSmoothRestriction K unitChartTest unitChartTest
      (fun _ => unitChartSymbol_continuous) (fun _ => unitChartSymbol_smooth) x = 1 := by
  rcases x with ⟨y, ξ⟩
  rw [finiteSmoothRestriction_apply]
  simp [unitChartTest, unitChartSymbol]

private theorem sum_groupRow_two {I : Type} [Fintype I] [DecidableEq I]
    (i j : I) (b : I → ℂ) :
    (∑ k, groupRow (![i,j] : Fin 2 → I) (![1,-1] : Fin 2 → ℂ) k * b k) = b i - b j := by
  simp only [groupRow, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

private theorem quadratic_groupRow_two {I : Type} [Fintype I] [DecidableEq I]
    (i j : I) (D : Matrix I I ℂ) :
    quadratic D (groupRow (![i,j] : Fin 2 → I) (![1,-1] : Fin 2 → ℂ)) =
      D i i - D i j - D j i + D j j := by
  rw [quadratic_groupRow]
  simp [Fin.sum_univ_two, sub_eq_add_neg, add_assoc]

/-- Equality of two local input components enforces equality of the corresponding
physical rows of the very same measure. Only its actual constant test is used. -/
theorem ae_physicalDensity_rows_eq_of_unit_test {I : Type} [Fintype I] [DecidableEq I]
    (K : BallData) (ν : (I → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (u : ℕ → I → ComplexL2 Space) (σ : ℕ → ℕ)
    (hPSD : ∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef)
    (hLimit : ∀ i j,
      Tendsto (fun n => inner ℂ (u (σ n) i)
        (finiteSeparableOperator unitChartTest unitChartTest (u (σ n) j)))
        atTop (𝓝 (∫ x, density ν hfin x i j ∂traceMeasure ν)))
    (i j : I) (heq : ∀ n, u n i = u n j) :
    ∀ᵐ x ∂traceMeasure ν, ∀ k, (density ν hfin x)ᵀ i k = (density ν hfin x)ᵀ j k := by
  let τ := traceMeasure ν
  let D := density ν hfin
  let R := groupRow (![i,j] : Fin 2 → I) (![1,-1] : Fin 2 → ℂ)
  have h₁ : (∫ x, D x i j ∂τ) = ∫ x, D x j j ∂τ :=
    tendsto_nhds_unique (by simpa only [heq] using hLimit i j) (hLimit j j)
  have h₂ : (∫ x, D x j i ∂τ) = ∫ x, D x j j ∂τ :=
    tendsto_nhds_unique (by simpa only [heq] using hLimit j i) (hLimit j j)
  have h₃ : (∫ x, D x i i ∂τ) = ∫ x, D x j j ∂τ :=
    tendsto_nhds_unique (by simpa only [heq] using hLimit i i) (hLimit j j)
  have hi (a b : I) : Integrable (fun x => D x a b) τ := integrable_density_entry ν hfin a b
  have hInt : Integrable (fun x => quadratic (D x) R) τ := by
    simpa only [R, quadratic_groupRow_two] using
      (((hi i i).sub (hi i j)).sub (hi j i)).add (hi j j)
  have hq : (∫ x, quadratic (D x) R ∂τ) = 0 := by
    have hadd := integral_add (((hi i i).sub (hi i j)).sub (hi j i)) (hi j j)
    have hsub := integral_sub ((hi i i).sub (hi i j)) (hi j i)
    simp only [Pi.sub_apply] at hadd hsub
    simp only [R, quadratic_groupRow_two]
    rw [hadd, hsub, integral_sub (hi i i) (hi i j), h₁, h₂, h₃,
      sub_self, zero_sub, neg_add_cancel]
  have hk := ae_quadratic_zero_and_row_kernel_of_integral_zero τ D (fun _ => R) hPSD hInt hq
  filter_upwards [hk] with x hx k
  have hk := congrFun hx.2 k
  change (∑ t, R t * (D x)ᵀ t k) = 0 at hk
  exact sub_eq_zero.mp ((sum_groupRow_two i j (fun t => (D x)ᵀ t k)).symm.trans hk)

/-- Ordered symmetric tensor input components give pointwise symmetric physical
rows on the common trace-conull set. This takes the established pairing limits
for the fixed subsequence and contracts the already selected trace density. -/
theorem ae_chartPhysicalCovariance_symmetry_of_same_pairings
    (K : BallData) (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (u : ℕ → JetSlot → ComplexL2 Space) (σ : ℕ → ℕ)
    (hPSD : ∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef)
    (hLimits : ∀ (J : Type) [Fintype J] (a m : J → BoundedSymbol Space)
        (ha : ∀ j, Continuous (a j : Space → ℂ))
        (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
        (_ : ∀ j, DegreeZero (m j : Space → ℂ)) (i j : JetSlot),
      let q := finiteSmoothRestriction K a m ha hm
      Tendsto (fun n => inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j)))
        atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν)))
    (hSym : ∀ n a b c, u n (a,b,c) = u n (a,c,b)) :
    ∀ᵐ x ∂traceMeasure ν, ∀ a b c (j : JetSlot),
      chartPhysicalCovariance K ν hfin x (a,b,c) j =
        chartPhysicalCovariance K ν hfin x (a,c,b) j := by
  have hLimit (i j : JetSlot) : Tendsto (fun n => inner ℂ (u (σ n) i)
        (finiteSeparableOperator unitChartTest unitChartTest (u (σ n) j)))
        atTop (𝓝 (∫ x, density ν hfin x i j ∂traceMeasure ν)) := by
    simpa only [unitChartRestriction_apply, one_mul] using
      hLimits Unit unitChartTest unitChartTest (fun _ => unitChartSymbol_continuous)
        (fun _ => unitChartSymbol_smooth) (fun _ => unitChartSymbol_degreeZero) i j
  have hs (i : JetSlot) : ∀ᵐ x ∂traceMeasure ν, ∀ k,
      chartPhysicalCovariance K ν hfin x i k =
        chartPhysicalCovariance K ν hfin x (i.1,i.2.2,i.2.1) k :=
    ae_physicalDensity_rows_eq_of_unit_test K ν hfin u σ hPSD hLimit i
      (i.1,i.2.2,i.2.1) (fun n => hSym n i.1 i.2.1 i.2.2)
  have h := ae_all_iff.mpr hs
  exact h.mono fun _ hx a b c j => hx (a,b,c) j

/-- Real source component symmetry is preserved by the actual common-cutoff
Schwartz and complex L² conversion used by the pairing producer. -/
theorem sourceSchwartz_toLp_ordered_symmetry
    (f : ℕ → JetSlot → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hSym : ∀ n a b c, f n (a,b,c) = f n (a,c,b))
    (n : ℕ) (a b c : Burnett.RicciSymbol.Index) :
    (sourceSchwartz (hs n (a,b,c)) χ₀ (hχ₀ n (a,b,c))).toLp 2 volume =
      (sourceSchwartz (hs n (a,c,b)) χ₀ (hχ₀ n (a,c,b))).toLp 2 volume := by
  apply congrArg (fun s : SchwartzMap Space ℂ => s.toLp 2 volume)
  apply SchwartzMap.ext
  intro x
  exact congrArg (fun g : Space → ℝ => (g x : ℂ)) (hSym n a b c)

end Burnett.Microlocal.FixedChartGeometricDensity
