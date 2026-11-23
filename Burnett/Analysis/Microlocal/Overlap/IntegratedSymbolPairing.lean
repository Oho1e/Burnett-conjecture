import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.SeparablePositive Burnett.Microlocal.SmoothBaseTests Burnett.Microlocal.SmoothAngularTests
open scoped ContDiff InnerProduct Topology

/-- An integrably bounded superposition of actual separated tests has the
corresponding integrated-symbol pairing on the same chart trace. -/
theorem tendsto_integrated_separablePairings_of_matrixDensity
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [SFinite μ]
    (K : BallData) (w : ℕ → JetSlot → ComplexL2 Space)
    (σ : ℕ → ℕ) (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings K w σ ν hfin)
    (a m : Y → BoundedSymbol Space)
    (ha : ∀ y, Continuous (a y : Space → ℂ))
    (hm : ∀ y, ContDiffOn ℝ ∞ (m y : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ y, DegreeZero (m y : Space → ℂ))
    (i j : JetSlot) (B : ℝ) (hB : ∀ n, ‖w (σ n) i‖ * ‖w (σ n) j‖ ≤ B)
    (b : Y → ℝ) (hb : Integrable b μ) (hbound : ∀ y, (a y).bound * (m y).bound ≤ b y)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun y => inner ℂ (w (σ n) i) (separableOperator (a y) (m y) (w (σ n) j))) μ)
    (hJoint : AEStronglyMeasurable
      (fun p : Y × Chart K => a p.1 p.2.1 * m p.1 p.2.2 * density ν hfin p.2 i j)
      (μ.prod (traceMeasure ν))) :
    Tendsto (fun n => ∫ y, inner ℂ (w (σ n) i) (separableOperator (a y) (m y) (w (σ n) j)) ∂μ)
      atTop (𝓝 (∫ x, (∫ y, a y x.1 * m y x.2 ∂μ) * density ν hfin x i j ∂traceMeasure ν)) := by
  let ρ (x : Chart K) := density ν hfin x i j
  let P (n : ℕ) (y : Y) := inner ℂ (w (σ n) i) (separableOperator (a y) (m y) (w (σ n) j))
  let F (y : Y) (x : Chart K) := a y x.1 * m y x.2 * ρ x
  let τ := traceMeasure ν
  letI : IsFiniteMeasure τ := hRep.2.1
  have hDCT : Tendsto (fun n => ∫ y, P n y ∂μ) atTop (𝓝 (∫ y, ∫ x, F y x ∂τ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun y => B * b y) hMeas (hb.const_mul B)
    · intro n
      filter_upwards with y
      have hOp : ‖separableOperator (a y) (m y) (w (σ n) j)‖ ≤
          (a y).bound * ((m y).bound * ‖w (σ n) j‖) :=
        (symbolL2_norm_le (a y) (fourierMultiplier (m y) (w (σ n) j))).trans
          (mul_le_mul_of_nonneg_left (fourierMultiplier_norm_le _ _) (a y).bound_nonneg)
      calc
        ‖P n y‖ ≤ ‖w (σ n) i‖ * ((a y).bound * ((m y).bound * ‖w (σ n) j‖)) :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hOp (norm_nonneg _))
        _ = (‖w (σ n) i‖ * ‖w (σ n) j‖) * ((a y).bound * (m y).bound) := by ring
        _ ≤ B * b y := mul_le_mul (hB n) (hbound y)
          (mul_nonneg (a y).bound_nonneg (m y).bound_nonneg)
          ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hB n))
    · filter_upwards with y
      have hSymbol (x : Chart K) :
          finiteSmoothRestriction K (fun _ : Unit => a y) (fun _ : Unit => m y)
            (fun _ => ha y) (fun _ => hm y) x = a y x.1 * m y x.2 := by
        rcases x with ⟨p, ξ⟩
        rw [finiteSmoothRestriction_apply]
        simp
      have h := hRep.2.2.2.2.2.2 Unit (fun _ => a y) (fun _ => m y)
        (fun _ => ha y) (fun _ => hm y) (fun _ => hd y) i j
      simpa [P, F, τ, ρ, finiteSeparableOperator, hSymbol] using h
  have hIntegrable : Integrable (Function.uncurry F) (μ.prod τ) := by
    refine (hb.mul_prod (integrable_density_entry ν hfin i j).norm).mono' hJoint ?_
    filter_upwards with p
    simp only [Function.uncurry, F, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul ((a p.1).norm_le p.2.1) ((m p.1).norm_le p.2.2)
        (norm_nonneg _) (a p.1).bound_nonneg).trans (hbound p.1)) (norm_nonneg _)
  have hSwap : (∫ y, ∫ x, F y x ∂τ ∂μ) =
      ∫ x, (∫ y, a y x.1 * m y x.2 ∂μ) * ρ x ∂τ := by
    rw [integral_integral_swap hIntegrable]
    apply integral_congr_ae
    filter_upwards with x
    exact integral_mul_const _ _
  simpa only [hSwap] using hDCT

end Burnett.Microlocal.Overlap
