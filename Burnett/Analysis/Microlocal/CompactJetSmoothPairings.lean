import Burnett.Analysis.Microlocal.FixedSubsequenceSeparableLimits
import Burnett.Analysis.Microlocal.CompactJetMatrixDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.FixedSubsequenceSeparableExtension

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.AngularCommutator
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CompactChartDensity (exists_compactChartMatrixDensity_of_localized_weak_zero)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexOrder Matrix

/-- The common chart density represents every finite separated test, with the same
subsequence and the same exact complex measures and trace. -/
theorem exists_compactChartMatrixDensity_allFiniteSmoothPairings {ι : Type}
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
      ∃ ν : (ι → ℂ) → Measure (Chart K),
      ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        (∀ v, (ν v).Regular) ∧ IsFiniteMeasure (traceMeasure ν) ∧
        (∀ s : Set (Chart K), MeasurableSet s →
          Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ)) ∧
        (∀ i j, entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure) ∧
        (∀ s : Set (Chart K), MeasurableSet s → ∀ i j,
          (∫ x in s, density ν hfin x i j ∂traceMeasure ν) = entryMeasure ν hfin i j s) ∧
        (∀ᵐ x ∂traceMeasure ν, (density ν hfin x).PosSemidef ∧ Matrix.trace (density ν hfin x) = 1) ∧
        ∀ (J : Type) [Fintype J] (a m : J → BoundedSymbol Space)
            (ha : ∀ j, Continuous (a j : Space → ℂ))
            (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
            (_ : ∀ j, DegreeZero (m j : Space → ℂ)) (i j : ι),
          let q := finiteSmoothRestriction K a m ha hm
          Tendsto (fun n => inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j)))
            atTop (𝓝 (∫ x, q x * density ν hfin x i j ∂traceMeasure ν)) := by
  intro u
  obtain ⟨σ, hσ, F, ν, hfin, hReg, _, hRep, hPair, _, hPSD, hTraceFin, hAC, hSet, hDensity⟩ :=
    exists_compactChartMatrixDensity_of_localized_weak_zero K f hs hf χ₀ hχ₀ hKf B hB ht
  have hF (ps : SeparableParameters) (i j : ι) :
      Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
        atTop (𝓝 (F i j (separableRestriction K ps))) := by
    rw [(hRep i j (separableRestriction K ps)).2]
    exact hPair ps i j
  refine ⟨σ, hσ, ν, hfin, hReg, hTraceFin, hPSD, hAC, hSet, hDensity, ?_⟩
  intro J _ a m ha hm hd i j
  dsimp only
  rw [← (hRep i j (finiteSmoothRestriction K a m ha hm)).2]
  exact tendsto_finiteSmoothPairing_of_commonListLimits_localized_weak_zero
    K a m ha hm hd f hs hf χ₀ hχ₀ hKf B hB ht σ hσ F hF i j

end Burnett.Microlocal.FixedSubsequenceSeparableExtension
