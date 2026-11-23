import Burnett.Analysis.Microlocal.AuxiliaryCovectorScale
import Burnett.Analysis.Microlocal.RoundChartCovariance
import Burnett.Analysis.Microlocal.FixedSubsequenceSeparableLimits

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.FixedChartGeometricDensity

open MeasureTheory Filter Set Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open scoped InnerProduct BigOperators ContDiff ComplexConjugate ComplexOrder Matrix Topology

/-- The auxiliary-normalized amplitude density is contracted from the same physical covariance. -/
def chartAmplitudeDensity (K : BallData) (rInv : K.Point → Tensor2)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (x : Chart K) : Matrix Pair Pair ℂ :=
  auxiliaryAmplitudeCovariance (rInv x.1) (auxiliaryUnitCovector (rInv x.1) (roundCovector x))
    (chartPhysicalCovariance K ν hfin x)

private theorem continuous_roundCovector {K : BallData} (a : Index) :
    Continuous (fun x : Chart K => roundCovector x a) :=
  ((sphereCoordinate a).continuous.comp continuous_snd).congr
    (fun x => sphereCoordinate_apply a x.2)

private theorem continuous_auxiliaryUnitCovector (K : BallData) (rInv : K.Point → Tensor2)
    (hr : ∀ a b, Continuous (fun p => rInv p a b))
    (haux : ∀ x : Chart K, 0 < symbolNorm (rInv x.1) (roundCovector x)) (a : Index) :
    Continuous (fun x : Chart K => auxiliaryUnitCovector (rInv x.1) (roundCovector x) a) := by
  have hnorm : Continuous (fun x : Chart K => symbolNorm (rInv x.1) (roundCovector x)) :=
    continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
      ((hr b c).comp continuous_fst |>.mul (continuous_roundCovector b)).mul
        (continuous_roundCovector c)
  exact ((Real.continuous_sqrt.comp hnorm).inv₀
    (fun x => (Real.sqrt_pos.mpr (haux x)).ne')).mul (continuous_roundCovector a)

theorem integrable_chartAmplitudeDensity_entry (K : BallData) (rInv : K.Point → Tensor2)
    (hr : ∀ a b, Continuous (fun p => rInv p a b))
    (haux : ∀ x : Chart K, 0 < symbolNorm (rInv x.1) (roundCovector x))
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) :
    Integrable (fun x => chartAmplitudeDensity K rInv ν hfin x i j) (traceMeasure ν) := by
  let C (x : Chart K) := gradientContraction
    (raiseCovector (rInv x.1) (auxiliaryUnitCovector (rInv x.1) (roundCovector x)))
  have hc (a : Pair) (k : JetSlot) : Continuous (fun x => C x a k) := by
    have h (b : Index) : Continuous (fun x : Chart K => raiseCovector (rInv x.1)
        (auxiliaryUnitCovector (rInv x.1) (roundCovector x)) b) :=
      continuous_finset_sum _ fun c _ => ((hr b c).comp continuous_fst).mul
        (continuous_auxiliaryUnitCovector K rInv hr haux c)
    by_cases he : k.2 = a
    · simpa only [C, gradientContraction, if_pos he] using
        Complex.continuous_ofReal.comp (h k.1)
    · simp only [C, gradientContraction, if_neg he, continuous_const]
  let M := chartPhysicalCovariance K ν hfin
  have ht (k l : JetSlot) : Integrable (fun x => C x i l * M x l k * conj (C x j k))
      (traceMeasure ν) := by
    let c : C(Chart K, ℂ) :=
      ⟨fun x => C x i l * conj (C x j k),
        (hc i l).mul (Complex.continuous_conj.comp (hc j k))⟩
    have h := (integrable_density_entry ν hfin k l).bdd_mul c.continuous.aestronglyMeasurable
      ⟨‖c‖, ContinuousMap.norm_coe_le_norm c⟩
    convert h using 1
    ext x
    change C x i l * M x l k * conj (C x j k) = (C x i l * conj (C x j k)) * M x l k
    ring
  change Integrable (fun x => (C x * M x * (C x)ᴴ) i j) (traceMeasure ν)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  exact integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => ht k l

/-- The actual complex amplitude measure in ordered, covariant coordinate components. -/
def chartAmplitudeMeasure (K : BallData) (rInv : K.Point → Tensor2)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) : ComplexMeasure (Chart K) :=
  (traceMeasure ν).withDensityᵥ (fun x => chartAmplitudeDensity K rInv ν hfin x i j)

theorem chartAmplitudeMeasure_apply (K : BallData) (rInv : K.Point → Tensor2)
    (hr : ∀ a b, Continuous (fun p => rInv p a b))
    (haux : ∀ x : Chart K, 0 < symbolNorm (rInv x.1) (roundCovector x))
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) (s : Set (Chart K)) (hs : MeasurableSet s) :
    chartAmplitudeMeasure K rInv ν hfin i j s =
      ∫ x in s, chartAmplitudeDensity K rInv ν hfin x i j ∂traceMeasure ν :=
  withDensityᵥ_apply (integrable_chartAmplitudeDensity_entry K rInv hr haux ν hfin i j) hs

/-- Each Borel set has a positive Hermitian amplitude covariance matrix. -/
theorem chartAmplitudeMeasure_positive (K : BallData) (rInv : K.Point → Tensor2)
    (hr : ∀ a b, Continuous (fun p => rInv p a b))
    (haux : ∀ x : Chart K, 0 < symbolNorm (rInv x.1) (roundCovector x))
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hPSD : ∀ᵐ x ∂traceMeasure ν, (chartAmplitudeDensity K rInv ν hfin x).PosSemidef)
    (s : Set (Chart K)) (hs : MeasurableSet s) :
    Matrix.PosSemidef (fun i j => chartAmplitudeMeasure K rInv ν hfin i j s : Matrix Pair Pair ℂ) := by
  let S := chartAmplitudeDensity K rInv ν hfin
  let τ := (traceMeasure ν).restrict s
  let A : Matrix Pair Pair ℂ := fun i j => chartAmplitudeMeasure K rInv ν hfin i j s
  have hA (i j) : A i j = ∫ x, S x i j ∂τ :=
    chartAmplitudeMeasure_apply K rInv hr haux ν hfin i j s hs
  have hS : ∀ᵐ x ∂τ, (S x).PosSemidef := ae_restrict_of_ae hPSD
  refine ⟨?_, fun v => ?_⟩
  · change Aᴴ = A
    ext i j
    rw [Matrix.conjTranspose_apply, Complex.star_def, hA j i, hA i j, ← integral_conj]
    apply integral_congr_ae
    filter_upwards [hS] with x hx
    exact congrFun (congrFun hx.1 i) j
  · let Q (x : Chart K) := star v ⬝ᵥ (S x *ᵥ v)
    have hQ (x : Chart K) : Q x = ∑ i, ∑ j, (star (v i) * v j) * S x i j := by
      simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hInt (i j : Pair) : Integrable (fun x => (star (v i) * v j) * S x i j) τ :=
      ((integrable_chartAmplitudeDensity_entry K rInv hr haux ν hfin i j).integrableOn).const_mul _
    have hQInt : Integrable Q τ := by
      exact (integrable_finset_sum Finset.univ fun i _ => integrable_finset_sum Finset.univ
        fun j _ => hInt i j).congr (Eventually.of_forall fun x => (hQ x).symm)
    have hQA : star v ⬝ᵥ (A *ᵥ v) = ∫ x, Q x ∂τ := by
      simp only [hQ, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hInt i j]
      simp only [integral_finset_sum _ fun j _ => hInt _ j, integral_const_mul, ← hA,
        dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hQA, Complex.nonneg_iff]
    have hQSign : ∀ᵐ x ∂τ, 0 ≤ (Q x).re ∧ (Q x).im = 0 := by
      filter_upwards [hS] with x hx
      have h := Complex.nonneg_iff.mp (hx.2 v)
      exact ⟨h.1, h.2.symm⟩
    change 0 ≤ RCLike.re (∫ x, Q x ∂τ) ∧ 0 = RCLike.im (∫ x, Q x ∂τ)
    rw [← integral_re hQInt, ← integral_im hQInt]
    refine ⟨integral_nonneg_of_ae (hQSign.mono fun _ hx => hx.1), ?_⟩
    exact (integral_eq_zero_of_ae (hQSign.mono fun _ hx => hx.2)).symm

theorem chartAmplitudeMeasure_zero_of_trace_null (K : BallData) (rInv : K.Point → Tensor2)
    (hr : ∀ a b, Continuous (fun p => rInv p a b))
    (haux : ∀ x : Chart K, 0 < symbolNorm (rInv x.1) (roundCovector x))
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) (s : Set (Chart K)) (hs : MeasurableSet s) (hnull : traceMeasure ν s = 0) :
    chartAmplitudeMeasure K rInv ν hfin i j s = 0 := by
  rw [chartAmplitudeMeasure_apply K rInv hr haux ν hfin i j s hs,
    Measure.restrict_zero_set hnull, integral_zero_measure]

/-- The earlier actual pairing limits rewritten with the same auxiliary-unit
amplitude. The index order at the amplitude is reversed because the input limits
use the Lean operator-second inner product. -/
theorem tendsto_chartPairing_of_same_amplitude_factorization
    (K : BallData) (rInv : K.Point → Tensor2)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hFactor : ∀ᵐ x ∂traceMeasure ν, ∀ i j,
      let ξr := auxiliaryUnitCovector (rInv x.1) (roundCovector x)
      chartPhysicalCovariance K ν hfin x i j =
        (ξr i.1 : ℂ) * (ξr j.1 : ℂ) * chartAmplitudeDensity K rInv ν hfin x i.2 j.2)
    (u : ℕ → JetSlot → ComplexL2 Space) (σ : ℕ → ℕ)
    {J : Type} [Fintype J] (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (i j : JetSlot)
    (hLimit : let q := finiteSmoothRestriction K a m ha hm
      Tendsto (fun n => inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j)))
        atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν))) :
    let q := finiteSmoothRestriction K a m ha hm
    Tendsto (fun n => inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j)))
      atTop (𝓝 (∫ x,
        let ξr := auxiliaryUnitCovector (rInv x.1) (roundCovector x)
        q x * ((ξr j.1 : ℂ) * (ξr i.1 : ℂ) *
          chartAmplitudeDensity K rInv ν hfin x j.2 i.2) ∂traceMeasure ν)) := by
  intro q
  change Filter.Tendsto _ _ (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν)) at hLimit
  convert hLimit using 2
  apply integral_congr_ae
  filter_upwards [hFactor] with x hx
  exact congrArg (fun z => q x * z) (hx j i).symm

end Burnett.Microlocal.FixedChartGeometricDensity
