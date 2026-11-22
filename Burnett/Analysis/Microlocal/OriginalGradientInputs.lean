import Burnett.Analysis.Microlocal.OriginalCoordinateCurl

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OriginalCoordinateCurl

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.F05.CoordinateCurl
open Burnett.X02.SobolevTestJet
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The original cutoff raw-gradient sheet supplies the exact real Fourier
inputs. One fixed outer cutoff and one L² bound work for all output slots
and all indices of the original sequence. -/
theorem exists_originalGradient_sourceSchwartz_inputs (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀)
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : Space → ℝ), (θ : Space → ℝ) x = 1) :
    ∃ f : ℕ → JetIndex → Space → ℝ,
    ∃ hs : ∀ n k, ContDiff ℝ ∞ (f n k),
    ∃ hf : ∀ n k, MemLp (f n k) 2 (volume : Measure Space),
    ∃ χ₀ : D, ∃ hχ₀ : ∀ n k x, f n k x ≠ 0 → (χ₀ : Space → ℝ) x = 1,
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ n k, ‖(hf n k).toLp (f n k)‖ ≤ B) ∧
      (∀ (k : JetIndex) (φ : D),
        Tendsto (fun n => ∫ x, f n k x * (φ : Space → ℝ) x) atTop (𝓝 0)) ∧
      (∀ n k x, f n k x = (χ : Space → ℝ) x * coordinateJet
        (fun y => metricComponents (coordinateBilinear (g n) c) y -
          metricComponents (coordinateBilinear g₀ c) y) x k.1 k.2.1 k.2.2) ∧
      (∀ n k, tsupport (f n k) ⊆ tsupport (χ : Space → ℝ)) ∧
      (∀ n, (fun k => sourceSchwartz (hs n k) χ₀ (hχ₀ n k)) =
        originalGradientSchwartz g₀ g h₀ hg c χ hχ n) ∧ χ₀ = θ := by
  let U := (chartAt CoordinateSpace c).target
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  let H := originalComponent g₀ g c
  have hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U := originalComponent_smoothOn g₀ g h₀ hg c
  let F (n : ℕ) (k : JetIndex) := localizedGradientTest hU χ hχ (hH n k.2) k.1
  let f (n : ℕ) (k : JetIndex) := (F n k : Space → ℝ)
  let hs (n : ℕ) (k : JetIndex) := test_smooth (F n k)
  let hf (n : ℕ) (k : JetIndex) := test_memLp (F n k)
  have hsupp (n : ℕ) (k : JetIndex) :
      tsupport (f n k) ⊆ tsupport (χ : Space → ℝ) :=
    localizedGradient_tsupport χ (H n k.2) k.1
  have hloc (n : ℕ) (k : JetIndex) (x : Space) (hx : f n k x ≠ 0) :
      (θ : Space → ℝ) x = 1 := hθ x (hsupp n k (subset_tsupport (f n k) hx))
  obtain ⟨A,hA,hD⟩ := exists_rawComponentDerivative_bound_of_original r g₀ g h₀ hg hn₀
    hconv hb c (tsupport (χ : Space → ℝ)) (test_compactSupport χ) hχ
  refine ⟨f,hs,hf,θ,hloc,A * ‖valueLp χ‖,mul_nonneg hA (norm_nonneg _),?_,?_,?_,hsupp,?_,rfl⟩
  · intro n k
    exact localizedGradientTest_L2_bound hU χ hχ (hH n k.2) k.1 hA
      (fun x hx => hD n k.2 k.1 x hx)
  · intro k φ
    exact localizedGradientTest_test_tendsto_zero hU χ hχ (fun n => H n k.2)
      (fun n => hH n k.2) (originalComponent_localUniform r g₀ g hconv c k.2) k.1 φ
  · intro n k x
    rfl
  · intro n
    funext k
    exact SchwartzMap.ext fun _ => rfl

end Burnett.F05.OriginalCoordinateCurl
